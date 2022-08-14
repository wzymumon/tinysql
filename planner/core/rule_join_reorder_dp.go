// Copyright 2018 PingCAP, Inc.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// See the License for the specific language governing permissions and
// limitations under the License.

package core

import (
	"math/bits"

	"github.com/pingcap/tidb/expression"
	"github.com/pingcap/tidb/parser/ast"
)

type joinReorderDPSolver struct {
	*baseSingleGroupJoinOrderSolver
	newJoin func(lChild, rChild LogicalPlan, eqConds []*expression.ScalarFunction, otherConds []expression.Expression) LogicalPlan
}

type joinGroupEqEdge struct {
	nodeIDs []int
	edge    *expression.ScalarFunction
}

type joinGroupNonEqEdge struct {
	nodeIDs []int
	// Use the binary representation of `nodeIDMask` to represent the nodes participating in Edge.
	nodeIDMask uint
	expr       expression.Expression
}

func (s *joinReorderDPSolver) solve(joinGroup []LogicalPlan, eqConds []expression.Expression) (LogicalPlan, error) {
	// TODO: You need to implement the join reorder algo based on DP.
	// The pseudo code can be found in README.
	// And there's some common struct and method like `baseNodeCumCost`, `calcJoinCumCost` you can use in `rule_join_reorder.go`.
	// Also, you can take a look at `rule_join_reorder_greedy.go`, this file implement the join reorder algo based on greedy algorithm.
	// You'll see some common usages in the greedy version.

	// Note that the join tree may be disconnected. i.e. You need to consider the case `select * from t, t1, t2`.
	for _, node := range joinGroup {
		_, err := node.recursiveDeriveStats()
		if err != nil {
			return nil, err
		}
		s.curJoinGroup = append(s.curJoinGroup, &jrNode{
			p:       node,
			cumCost: s.baseNodeCumCost(node),
		})
	}
	// Create an adjacency matrix to represent the node graph
	nodeGraph := make([][]int, len(s.curJoinGroup))
	totalEqEdges := make([]joinGroupEqEdge, 0, len(eqConds))
	for _, cond := range eqConds {
		sf := cond.(*expression.ScalarFunction)
		lCol := sf.GetArgs()[0].(*expression.Column)
		rCol := sf.GetArgs()[1].(*expression.Column)
		lIdx, err := findNodeIndexInGroup(joinGroup, lCol)
		if err != nil {
			return nil, err
		}
		rIdx, err := findNodeIndexInGroup(joinGroup, rCol)
		if err != nil {
			return nil, err
		}
		// Statistics EqEdges
		totalEqEdges = append(totalEqEdges, joinGroupEqEdge{
			nodeIDs: []int{lIdx, rIdx},
			edge:    sf,
		})
		nodeGraph[lIdx] = append(nodeGraph[lIdx], rIdx)
		nodeGraph[rIdx] = append(nodeGraph[rIdx], lIdx)
	}

	// Statistics NonEqEdges
	totalNonEqEdges := make([]joinGroupNonEqEdge, 0, len(s.otherConds))
	for _, cond := range s.otherConds {
		cols := expression.ExtractColumns(cond)
		mask := uint(0)
		ids := make([]int, 0, len(cols))
		for _, col := range cols {
			idx, err := findNodeIndexInGroup(joinGroup, col)
			if err != nil {
				return nil, err
			}
			ids = append(ids, idx)
			mask |= 1 << uint(idx)
		}
		totalNonEqEdges = append(totalNonEqEdges, joinGroupNonEqEdge{
			nodeIDs:    ids,
			nodeIDMask: mask,
			expr:       cond,
		})
	}
	var cartesianGroup []LogicalPlan

	visited := make([]bool, len(joinGroup))
	nodeID2VisitID := make([]int, len(joinGroup))

	// BFS
	for i := 0; i < len(joinGroup); i++ {
		if visited[i] {
			continue
		}

		visitID2NodeID := s.bfsGraph(i, visited, nodeGraph, nodeID2VisitID)
		// Use the binary representation of `nodeIDMask`` to represent the nodes participating in join group.
		nodeIDMask := uint(0)
		for _, nodeID := range visitID2NodeID {
			nodeIDMask |= 1 << uint(nodeID)
		}

		var subNonEqEdges []joinGroupNonEqEdge
		for i := len(totalNonEqEdges) - 1; i >= 0; i++ {
			//
			if totalNonEqEdges[i].nodeIDMask&nodeIDMask != totalNonEqEdges[i].nodeIDMask {
				continue
			}
			newMask := uint(0)
			for _, nodeID := range totalNonEqEdges[i].nodeIDs {
				newMask |= 1 << uint(nodeID2VisitID[nodeID])
			}
			totalNonEqEdges[i].nodeIDMask = newMask
			subNonEqEdges = append(subNonEqEdges, totalNonEqEdges[i])
			totalNonEqEdges = append(totalNonEqEdges[:i], totalNonEqEdges[i+1:]...)
		}
		// Do DP on each sub graph.
		join, err := s.dpGraph(visitID2NodeID, nodeID2VisitID, joinGroup, totalEqEdges, subNonEqEdges)
		if err != nil {
			return nil, err
		}
		cartesianGroup = append(cartesianGroup, join)
	}

	remainedOtherConds := make([]expression.Expression, 0, len(totalNonEqEdges))
	for _, edge := range totalNonEqEdges {
		remainedOtherConds = append(remainedOtherConds, edge.expr)
	}
	return s.makeBushyJoin(cartesianGroup, remainedOtherConds), nil
}

// bfsGraph bfs a sub graph starting at startPos. And relabel its label for future use.
func (s *joinReorderDPSolver) bfsGraph(startNode int, visited []bool, nodeGraph [][]int, nodeID2VisitID []int) []int {
	queue := []int{startNode}
	visited[startNode] = true
	var visitID2NodeID []int
	for len(queue) > 0 {
		curNodeID := queue[0]
		queue = queue[1:]
		nodeID2VisitID[curNodeID] = len(visitID2NodeID)
		visitID2NodeID = append(visitID2NodeID, curNodeID)
		for _, nodeID := range nodeGraph[curNodeID] {
			if visited[nodeID] {
				continue
			}
			queue = append(queue, nodeID)
			visited[nodeID] = true
		}
	}
	return visitID2NodeID
}

// bestPlan[S:set of node] = the best one among Join(bestPlan[S1:subset of S], bestPlan[S2: S/S1])
func (s joinReorderDPSolver) dpGraph(visitID2NodeID, nodeID2VisitID []int, joinGroup []LogicalPlan,
	totalEqEdges []joinGroupEqEdge, totalNonEqEdges []joinGroupNonEqEdge) (LogicalPlan, error) {
	nodeCnt := uint(len(visitID2NodeID))
	searchSpace := uint(1 << nodeCnt)
	bestPlan := make([]*jrNode, searchSpace)
	for i := uint(0); i < nodeCnt; i++ {
		bestPlan[1<<i] = s.curJoinGroup[visitID2NodeID[i]]
	}

	for nodeBitmap := uint(1); nodeBitmap < searchSpace; nodeBitmap++ {
		if bits.OnesCount(nodeBitmap) == 1 {
			continue
		}
		// iterate over all substructures
		for sub := (nodeBitmap - 1) & nodeBitmap; sub > 0; sub = (sub - 1) & nodeBitmap {
			remain := nodeBitmap ^ sub
			if sub > remain {
				continue
			}
			if bestPlan[sub] == nil || bestPlan[remain] == nil {
				continue
			}
			// Get the edge connecting the two parts.
			var usedEqEdges []joinGroupEqEdge
			var otherConds []expression.Expression

			for _, edge := range totalEqEdges {
				lIdx := uint(nodeID2VisitID[edge.nodeIDs[0]])
				rIdx := uint(nodeID2VisitID[edge.nodeIDs[1]])
				if ((sub&(1<<lIdx)) > 0 && (remain&(1<<rIdx)) > 0) || ((sub&(1<<rIdx)) > 0 && (remain&(1<<lIdx)) > 0) {
					usedEqEdges = append(usedEqEdges, edge)
				}
			}
			for _, edge := range totalNonEqEdges {
				// If the result is false, means that the current group hasn't covered the columns involved in the expression.
				if edge.nodeIDMask&(sub|remain) != edge.nodeIDMask {
					continue
				}
				// Check whether this expression is only built from one side of the join.
				if edge.nodeIDMask&sub == 0 || edge.nodeIDMask&remain == 0 {
					continue
				}
				otherConds = append(otherConds, edge.expr)
			}

			if len(usedEqEdges) == 0 {
				continue
			}
			newJoin, err := s.newJoinWithEdge(bestPlan[sub].p, bestPlan[remain].p, totalEqEdges, otherConds)
			if err != nil {
				return nil, err
			}
			curCost := s.calcJoinCumCost(newJoin, bestPlan[sub], bestPlan[remain])
			if bestPlan[nodeBitmap] == nil {
				bestPlan[nodeBitmap] = &jrNode{
					p:       newJoin,
					cumCost: curCost,
				}
			} else if bestPlan[nodeBitmap].cumCost > curCost {
				bestPlan[nodeBitmap].p = newJoin
				bestPlan[nodeBitmap].cumCost = curCost
			}

		}
	}
	return bestPlan[len(bestPlan)-1].p, nil
}

func (s *joinReorderDPSolver) newJoinWithEdge(leftPlan, rightPlan LogicalPlan, edges []joinGroupEqEdge, otherConds []expression.Expression) (LogicalPlan, error) {
	var eqConds []*expression.ScalarFunction
	for _, edge := range edges {
		lCol := edge.edge.GetArgs()[0].(*expression.Column)
		rCol := edge.edge.GetArgs()[1].(*expression.Column)
		if leftPlan.Schema().Contains(lCol) {
			eqConds = append(eqConds, edge.edge)
		} else {
			newSf := expression.NewFunctionInternal(s.ctx, ast.EQ, edge.edge.GetType(), rCol, lCol).(*expression.ScalarFunction)
			eqConds = append(eqConds, newSf)
		}
	}
	join := s.newJoin(leftPlan, rightPlan, eqConds, otherConds)
	_, err := join.recursiveDeriveStats()
	return join, err
}

// Make cartesian join as bushy tree.
func (s *joinReorderDPSolver) makeBushyJoin(cartesianJoinGroup []LogicalPlan, otherConds []expression.Expression) LogicalPlan {
	for len(cartesianJoinGroup) > 1 {
		resultJoinGroup := make([]LogicalPlan, 0, len(cartesianJoinGroup))
		for i := 0; i < len(cartesianJoinGroup); i += 2 {
			if i+1 == len(cartesianJoinGroup) {
				resultJoinGroup = append(resultJoinGroup, cartesianJoinGroup[i])
				break
			}
			// TODO:Since the other condition may involve more than two tables, e.g. t1.a = t2.b+t3.c.
			//  So We'll need a extra stage to deal with it.
			// Currently, we just add it when building cartesianJoinGroup.
			mergedSchema := expression.MergeSchema(cartesianJoinGroup[i].Schema(), cartesianJoinGroup[i+1].Schema())
			var usedOtherConds []expression.Expression
			otherConds, usedOtherConds = expression.FilterOutInPlace(otherConds, func(expr expression.Expression) bool {
				return expression.ExprFromSchema(expr, mergedSchema)
			})
			resultJoinGroup = append(resultJoinGroup, s.newJoin(cartesianJoinGroup[i], cartesianJoinGroup[i+1], nil, usedOtherConds))
		}
		cartesianJoinGroup = resultJoinGroup
	}
	return cartesianJoinGroup[0]
}

func findNodeIndexInGroup(group []LogicalPlan, col *expression.Column) (int, error) {
	for i, plan := range group {
		if plan.Schema().Contains(col) {
			return i, nil
		}
	}
	return -1, ErrUnknownColumn.GenWithStackByArgs(col, "JOIN REORDER RULE")
}
