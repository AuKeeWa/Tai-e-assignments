/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 *
 * Tai-e is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * Tai-e is distributed in the hope that it will be useful,but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with Tai-e. If not, see <https://www.gnu.org/licenses/>.
 */

package pascal.taie.analysis.dataflow.solver;

import pascal.taie.analysis.dataflow.analysis.DataflowAnalysis;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.graph.cfg.CFG;

import java.util.LinkedList;
import java.util.Queue;

class WorkListSolver<Node, Fact> extends Solver<Node, Fact> {

    WorkListSolver(DataflowAnalysis<Node, Fact> analysis) {
        super(analysis);
    }

    @Override
    protected void doSolveForward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        // TODO - finish me
        Queue<Node> workList = new LinkedList<>(cfg.getNodes());
        while (!workList.isEmpty()) {
            Node node = workList.poll();//移除并返回队头node
            CPFact in = new CPFact();
            CPFact out = (CPFact) result.getOutFact(node);
            for (Node pred : cfg.getPredsOf(node))
                analysis.meetInto(result.getOutFact(pred), (Fact) in);
            if (analysis.transferNode(node, (Fact) in, (Fact) out))//可知此次transfer是否改变了out
                cfg.getSuccsOf(node).forEach(workList::offer);//后继节点插回队列
            result.setInFact(node, (Fact) in);
            result.setOutFact(node, (Fact) out);//刷新结果
        }
    }

    @Override
    protected void doSolveBackward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        // TODO - finish me
        boolean flag = true;
        while(flag){
            flag = false;
            for(Node t : cfg){
                if(!cfg.isExit(t)){
                    if(result.getOutFact(t) == null)
                        result.setOutFact(t, analysis.newInitialFact());
                    for(Node S : cfg.getSuccsOf(t)){
                        analysis.meetInto(result.getInFact(S), result.getOutFact(t));
                    }
                    // if there is any update then continue
                    if(analysis.transferNode(t, result.getInFact(t), result.getOutFact(t)))
                        flag = true;
                }
            }
        }
    }
}
