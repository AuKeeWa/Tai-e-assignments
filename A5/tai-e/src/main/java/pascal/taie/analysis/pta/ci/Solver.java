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

package pascal.taie.analysis.pta.ci;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.DefaultCallGraph;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.Copy;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.LoadArray;
import pascal.taie.ir.stmt.LoadField;
import pascal.taie.ir.stmt.New;
import pascal.taie.ir.stmt.StmtVisitor;
import pascal.taie.ir.stmt.StoreArray;
import pascal.taie.ir.stmt.StoreField;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JMethod;
import pascal.taie.util.AnalysisException;
import pascal.taie.language.type.Type;

import java.util.List;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final HeapModel heapModel;

    private DefaultCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private StmtProcessor stmtProcessor;

    private ClassHierarchy hierarchy;

    Solver(HeapModel heapModel) {
        this.heapModel = heapModel;
    }

    /**
     * Runs pointer analysis algorithm.
     */
    void solve() {
        initialize();
        analyze();
    }

    /**
     * Initializes pointer analysis.
     */
    private void initialize() {
        workList = new WorkList();
        pointerFlowGraph = new PointerFlowGraph();
        callGraph = new DefaultCallGraph();
        stmtProcessor = new StmtProcessor();
        hierarchy = World.get().getClassHierarchy();
        // initialize main method
        JMethod main = World.get().getMainMethod();
        callGraph.addEntryMethod(main);
        addReachable(main);
    }

    /**
     * Processes new reachable method.
     */
    private void addReachable(JMethod method) {
        // TODO - finish me
        if (!callGraph.contains(method)) {
            callGraph.addReachableMethod(method);
            method.getIR().getStmts().forEach(stmt -> {
                stmt.accept(stmtProcessor);
            });
        }
    }

    /**
     * Processes statements in new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {
        // TODO - if you choose to implement addReachable()
        //  via visitor pattern, then finish me

        @Override
        public Void visit(New stmt) {
            Pointer p = pointerFlowGraph.getVarPtr(stmt.getLValue());
            workList.addEntry(p, new PointsToSet(heapModel.getObj(stmt)));
            return null;
        }

        @Override
        public Void visit(Copy stmt) {
            addPFGEdge(
                    pointerFlowGraph.getVarPtr(stmt.getRValue()),
                    pointerFlowGraph.getVarPtr(stmt.getLValue())
            );
            return null;
        }

        @Override
        public Void visit(StoreField stmt) {
            if (stmt.isStatic()) {
                addPFGEdge(
                        pointerFlowGraph.getVarPtr(stmt.getRValue()),
                        pointerFlowGraph.getStaticField(stmt.getFieldRef().resolve())
                );
            }
            return null;
        }

        @Override
        public Void visit(LoadField stmt) {
            if (stmt.isStatic()) {
                addPFGEdge(
                        pointerFlowGraph.getStaticField(stmt.getFieldRef().resolve()),
                        pointerFlowGraph.getVarPtr(stmt.getLValue())
                );
            }
            return null;
        }

        /*@Override
        public Void visit(StoreArray stmt) {
            addPFGEdge(
                    pointerFlowGraph.getVarPtr(stmt.getRValue()),
                    pointerFlowGraph.getVarPtr(stmt.getArrayAccess().getIndex())
            );
            return null;
        }

        @Override
        public Void visit(LoadArray stmt) {
            addPFGEdge(
                    pointerFlowGraph.getVarPtr(stmt.getArrayAccess().getIndex()),
                    pointerFlowGraph.getVarPtr(stmt.getLValue())

            );
            return null;
        }*/

        @Override
        public Void visit(Invoke callSite) {
            if (callSite.isStatic()) {
                JMethod callee = resolveCallee(null, callSite);
                processSingleCall(callSite, callee);
            }
            return null;
        }
    }

    private void processSingleCall(Invoke callSite, JMethod method) {
        // if l->m ∉ CallGraph
        if (!callGraph.getCalleesOf(callSite).contains(method)) {
            CallKind callKind = CallGraphs.getCallKind(callSite);
            if (callKind != null) {
                // add l->m to CallGraph
                callGraph.addEdge(new Edge<>(callKind, callSite, method));
                addReachable(method);
                // 传参数
                // foreach parameter pi of m
                List<Var> args = method.getIR().getParams();
                for (int i = 0; i < args.size(); i++) {
                    // addEdge(ai,pi)
                    addPFGEdge(
                            pointerFlowGraph.getVarPtr(callSite.getRValue().getArg(i)),
                            pointerFlowGraph.getVarPtr(args.get(i))
                    );
                }
                // 传返回值
                Var r = callSite.getLValue();
                if (r != null) {
                    method.getIR().getReturnVars().forEach(ret ->
                    {
                        addPFGEdge(
                                pointerFlowGraph.getVarPtr(ret),
                                pointerFlowGraph.getVarPtr(r)
                        );
                    });
                }
            }
        }
    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        // TODO - finish me
        if (!pointerFlowGraph.getSuccsOf(source).contains(target)) {
            pointerFlowGraph.addEdge(source, target);
            PointsToSet pts = source.getPointsToSet();
            if (!pts.isEmpty()) {
                workList.addEntry(target, pts);
            }
        }
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
        // TODO - finish me
        while (!workList.isEmpty()) {
            WorkList.Entry entry = workList.pollEntry();
            Pointer pointer = entry.pointer();
            PointsToSet pts = entry.pointsToSet();
            PointsToSet delta = propagate(pointer, pts);
            if (pointer instanceof VarPtr ptr) {
                Var var = ptr.getVar();
                delta.forEach(obj -> {
                    var.getStoreFields().forEach(stmt -> {
                        addPFGEdge(
                                pointerFlowGraph.getVarPtr(stmt.getRValue()),
                                pointerFlowGraph.getInstanceField(obj, stmt.getFieldAccess().getFieldRef().resolve())
                        );
                    });
                    var.getLoadFields().forEach(stmt -> {
                        addPFGEdge(
                                pointerFlowGraph.getInstanceField(obj, stmt.getFieldAccess().getFieldRef().resolve()),
                                pointerFlowGraph.getVarPtr(stmt.getLValue())
                        );
                    });
                    var.getStoreArrays().forEach(stmt -> {
                        addPFGEdge(
                                pointerFlowGraph.getVarPtr(stmt.getRValue()),
                                pointerFlowGraph.getArrayIndex(obj)
                        );
                    });
                    var.getLoadArrays().forEach(stmt -> {
                        addPFGEdge(
                                pointerFlowGraph.getArrayIndex(obj),
                                pointerFlowGraph.getVarPtr(stmt.getLValue())
                        );
                    });
                    processCall(var, obj);
                });
            }
        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        // TODO - finish me
        // delta = pts - pt(n)
        // propagate(n,delta)
        PointsToSet delta = new PointsToSet();
        pointsToSet.objects()
                .filter(ptr -> !pointer.getPointsToSet().contains(ptr))
                .forEach(delta::addObject);
        if (!delta.isEmpty()) {
            delta.forEach(obj -> pointer.getPointsToSet().addObject(obj));
            pointerFlowGraph.getSuccsOf(pointer).forEach(succ -> workList.addEntry(succ, delta));
        }
        return delta;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param var  the variable that holds receiver objects
     * @param recv a new discovered object pointed by the variable.
     */
    private void processCall(Var var, Obj recv) {
        // TODO - finish me
        //l:r=x.k(a1,...,an) ∈ S    // var=x  recv = oi  callSite = k
        var.getInvokes().forEach(callSite -> {
            JMethod method = resolveCallee(recv, callSite);
            workList.addEntry(
                    pointerFlowGraph.getVarPtr(method.getIR().getThis()),
                    new PointsToSet(recv));
            processSingleCall(callSite, method);
        });
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv     the receiver object of the method call. If the callSite
     *                 is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(Obj recv, Invoke callSite) {
        Type type = recv != null ? recv.getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    CIPTAResult getResult() {
        return new CIPTAResult(pointerFlowGraph, callGraph);
    }
}
