// Copyright (c) 2016-2019 K Team. All Rights Reserved.

package org.kframework.backend.java.symbolic;

import org.kframework.backend.java.kil.ConstrainedTerm;
import org.kframework.backend.java.kil.GlobalContext;
import org.kframework.backend.java.util.FormulaContext;
import org.kframework.definition.Module;
import org.kframework.keq.KEqFrontEnd;
import org.kframework.keq.KEqOptions;
import org.kframework.kompile.CompiledDefinition;
import org.kframework.kore.K;
import org.kframework.unparser.ColorSetting;
import org.kframework.unparser.OutputModes;
import scala.Tuple2;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.concurrent.atomic.AtomicLong;
import java.util.concurrent.atomic.AtomicReference;
import java.util.stream.Collectors;

/**
 * Created by daejunpark on 8/15/16.
 */
public class EquivChecker {
    public static void trace(String msg) {
        if (KEqFrontEnd.globalKEqOptions.showTraces) System.out.println(msg);
    }
    public static void smt(String msg) { if (KEqFrontEnd.globalKEqOptions.showSMT) System.out.println(msg); }
    public static void debug(String msg) { System.out.println(msg); }

    public static void debug(String header, String msg)  {
        debug("[" + header + "] " + msg);
    }

    public static void smt(String header, String msg)  {
        smt("[" + header + "] " + msg);
    }

    public static void trace(String header, String msg)  {
        trace("[" + header + "] " + msg);
    }

    static int query_counter = 0;
    static File current_query_dir = null;

    public synchronized static void saveZ3Result(String query, String result, long time, ProcessBuilder proc) {
        if (KEqFrontEnd.globalKEqOptions.z3QueryLogDir != null) {
            try {
                if (current_query_dir == null) {
                    File dir = new File(KEqFrontEnd.globalKEqOptions.z3QueryLogDir);
                    if (!dir.exists()) {
                        dir.mkdir();
                    }

                    Path path = Files.createTempDirectory(Paths.get(dir.getPath()), "z3-query-");
                    current_query_dir = path.toFile();

                    System.out.println("storing z3 queries to " + current_query_dir.getAbsolutePath());
                }

                String command = String.join(" ", proc.command());

                File log = new File(current_query_dir, "q-" + query_counter + ".smt");
                log.createNewFile();

                FileWriter writer = new FileWriter(log);
                writer.write("; " + command + "\n\n");
                writer.write(query + "\n\n(check-sat)\n");
                writer.write("; " + result + ", took " + time + "ms\n");
                writer.close();

                query_counter += 1;
            } catch (IOException exc) {
                System.err.println(exc.toString());
            }
        }
    }

    private static long accumulatedZ3Time = 0;

    public static synchronized void addAccumulatedZ3Time(long ms) {
        accumulatedZ3Time += ms;
    }

    public static boolean equiv(
            java.util.List<ConstrainedTerm> startSyncNodes1,
            java.util.List<ConstrainedTerm> startSyncNodes2,
            java.util.List<ConstrainedTerm> targetSyncNodes1,
            java.util.List<ConstrainedTerm> targetSyncNodes2,
            java.util.List<ConjunctiveFormula> startEnsures,
            java.util.List<ConjunctiveFormula> targetEnsures,
            java.util.List<Boolean> trusted1,
            java.util.List<Boolean> trusted2,
            //
            SymbolicRewriter rewriter1,
            SymbolicRewriter rewriter2
    ) {
        assert startEnsures.size() == targetEnsures.size();
        assert targetSyncNodes1.size() == targetEnsures.size();
        assert targetSyncNodes2.size() == targetEnsures.size();
        assert KEqFrontEnd.globalKEqOptions.parallel >= 1;

        // do a full gc here
        Runtime.getRuntime().gc();

        int numSyncPoints = targetEnsures.size();

        java.util.List<Set<SyncNode>> allSyncNodes1 = newListOfSets(numSyncPoints);
        java.util.List<Set<SyncNode>> allSyncNodes2 = newListOfSets(numSyncPoints);

        // start with non-final nodes
        java.util.List<SyncNode> currSyncNodes1 = new ArrayList<>();
        java.util.List<SyncNode> currSyncNodes2 = new ArrayList<>();
        for (int i = 0; i < numSyncPoints; i++) {
            if (trusted1.get(i)) { assert trusted2.get(i); continue; }

            ConstrainedTerm t1 = startSyncNodes1.get(i);
            ConstrainedTerm t2 = startSyncNodes2.get(i);

            /* TODO: should final nodes be trusted?
            List<ConstrainedTerm> nt1 = rewriter1.fastComputeRewriteStep(t1, false, true, true);
            List<ConstrainedTerm> nt2 = rewriter2.fastComputeRewriteStep(t2, false, true, true);
            assert nt1.isEmpty() == nt2.isEmpty();
            if (nt1.isEmpty()) continue;
             */

            currSyncNodes1.add(new SyncNode(i, null, t1, null)); // TODO: check if null is safe
            currSyncNodes2.add(new SyncNode(i, null, t2, null));
        }

        while (!currSyncNodes1.isEmpty() && !currSyncNodes2.isEmpty()) {

            trace("################# Remaining unsync nodes in the LLVM side:");

            for (SyncNode node : currSyncNodes1) {
                trace("   - from sync point " + node.startSyncPoint + ": " + node.currSyncNode.toString());
            }

            trace("################# Remaining unsync nodes in the vx86 side:");

            for (SyncNode node : currSyncNodes2) {
                trace("   - from sync point " + node.startSyncPoint + ": " + node.currSyncNode.toString());
            }

            AtomicReference<java.util.List<Set<SyncNode>>> syncNodes1 = new AtomicReference<java.util.List<Set<SyncNode>>>(null);
            AtomicReference<java.util.List<Set<SyncNode>>> syncNodes2 = new AtomicReference<java.util.List<Set<SyncNode>>>(null);

            AtomicLong symExecTime1 = new AtomicLong(0);
            AtomicLong symExecTime2 = new AtomicLong(0);

            final long begin = System.currentTimeMillis();
            accumulatedZ3Time = 0;

            Runnable f1 = () -> {
                long begin1 = System.currentTimeMillis();
                syncNodes1.set(getNextSyncNodes("llvm", currSyncNodes1, targetSyncNodes1, rewriter1));
                symExecTime1.set(System.currentTimeMillis() - begin1);
            };

            Runnable f2 = () -> {
                long begin2 = System.currentTimeMillis();
                syncNodes2.set(getNextSyncNodes("vx86", currSyncNodes2, targetSyncNodes2, rewriter2));
                symExecTime2.set(System.currentTimeMillis() - begin2);
            };

            if (KEqFrontEnd.globalKEqOptions.parallel > 1) {
                Thread t1 = new Thread(f1);
                Thread t2 = new Thread(f2);

                t1.start(); t2.start();

                while (true) {
                    try {
                        t1.join();
                        break;
                    } catch (InterruptedException e) {
                        debug("t1 interrupted " + e.toString());
                    }
                }

                while (true) {
                    try {
                        t2.join();
                        break;
                    } catch (InterruptedException e) {
                        debug("t2 interrupted " + e.toString());
                    }
                }
            } else {
                f1.run();
                f2.run();
            }

            long elapsed = System.currentTimeMillis() - begin;

            debug("### end of one round of symbolic execution:");
            debug("  - symbolic execution total: " + (((double)elapsed) / 1000.0) + "s");
            debug("  - symbolic execution 1 total: " + (((double)symExecTime1.get()) / 1000.0) + "s");
            debug("  - symbolic execution 2 total: " + (((double)symExecTime2.get()) / 1000.0) + "s");
            debug("  - z3 total query time in symbolic execution: " + (((double)accumulatedZ3Time) / 1000.0) + "s");

            // fail
            if (syncNodes1.get() == null || syncNodes2.get() == null) return false; // TODO: output more information for failure

            long matchingBegin = System.currentTimeMillis();
            accumulatedZ3Time = 0;

            allSyncNodes1 = mergeListOfSets(allSyncNodes1, syncNodes1.get());
            allSyncNodes2 = mergeListOfSets(allSyncNodes2, syncNodes2.get());

            matchSyncNodes(allSyncNodes1, allSyncNodes2, startEnsures, targetEnsures);
            validateSyncNodes(allSyncNodes1);
            validateSyncNodes(allSyncNodes2);

            elapsed = System.currentTimeMillis() - matchingBegin;

            debug("### end of matching:");
            debug("  - matching total: " + (((double)elapsed) / 1000.0) + "s");
            debug("  - z3 total query time: " + (((double)accumulatedZ3Time) / 1000.0) + "s");

            currSyncNodes1.clear();
            currSyncNodes2.clear();
            for (int i = 0; i < numSyncPoints; i++) {
                for (SyncNode node : allSyncNodes1.get(i)) {
                    if (node.mark == Mark.RED) {
                        debug("[llvm] found a remaining state at sync point " + i);
                        trace(" - constrained term: " + node.currSyncNode.toString());
                        currSyncNodes1.add(node);
                    }
                }
                for (SyncNode node : allSyncNodes2.get(i)) {
                    if (node.mark == Mark.RED) {
                        debug("[x86] found a remaining state at sync point " + i);
                        trace(" - constrained term: " + node.currSyncNode.toString());
                        currSyncNodes2.add(node);
                    }
                }
            }

            if (currSyncNodes1.isEmpty() != currSyncNodes2.isEmpty()) {
                return false; // TODO: output more information for failure
            }
        }

        return true;
    }

    public static java.util.List<Set<SyncNode>> getNextSyncNodes(
            String name,
            java.util.List<SyncNode> currSyncNodes,
            java.util.List<ConstrainedTerm> targetSyncNodes,
            SymbolicRewriter rewriter
    ) {
        int numSyncPoints = targetSyncNodes.size();
        java.util.List<Set<SyncNode>> nextSyncNodes = newListOfSets(numSyncPoints);
        for (SyncNode currSyncNode : currSyncNodes) {
            java.util.List<Set<SyncNode>> nodes = getNextSyncNodes(name, currSyncNode, targetSyncNodes, rewriter);
            if (nodes == null) return null; // failed // TODO: output more information for failure
            nextSyncNodes = mergeListOfSets(nextSyncNodes, nodes);
        }
        return nextSyncNodes;
    }

    public static java.util.List<Set<SyncNode>> getNextSyncNodes(
            String name,
            SyncNode currSyncNode,
            java.util.List<ConstrainedTerm> targetSyncNodes,
            SymbolicRewriter rewriter
    ) {
        int numSyncPoints = targetSyncNodes.size();

        java.util.List<Set<SyncNode>> nextSyncNodes = newListOfSets(numSyncPoints);

        java.util.List<ConstrainedTerm> queue = new ArrayList<>();
        java.util.List<ConstrainedTerm> nextQueue = new ArrayList<>();

        ConstrainedTerm initTerm = currSyncNode.currSyncNode;
        queue.add(initTerm);

        int steps = 0;

        debug(name, "rewriting starts");
        trace(name, "from term: " + initTerm.toString());

        while (!queue.isEmpty()) {
            ++steps;

            debug(name, "#################### step " + steps + ", width: " + queue.size());

            for (ConstrainedTerm curr : queue) {
                trace(">>> from term: " + curr.toString());

                long begin = System.currentTimeMillis();
                // temporary fix for get_block_head_tail
                curr.termContext().setTopTerm(curr.term());
                java.util.List<ConstrainedTerm> nexts = rewriter.fastComputeRewriteStep(curr, false, true, true, steps,
                        initTerm);
                long elapsed = System.currentTimeMillis() - begin;
                debug(name, "rewriting took: " + elapsed + "ms");

                if (nexts.isEmpty()) {
                    /* final term */
                    debug(name, "!!! no possible rewrites");
                    return null; // failed // TODO: output more information for failure
                }

            loop:
                for (ConstrainedTerm next : nexts) {
                    trace(name, "==> to term: " + next.toString());

                    begin = System.currentTimeMillis();

                    for (int i = 0; i < numSyncPoints; i++) {
                        ConjunctiveFormula constraint = next.matchImplies(targetSyncNodes.get(i), true, false,
                                new FormulaContext(FormulaContext.Kind.EquivImplication, null, next.termContext().global()), null);
                        if (constraint != null) {
                            SyncNode node = new SyncNode(currSyncNode.startSyncPoint, currSyncNode, next, constraint);
                            nextSyncNodes.get(i).add(node);
                            debug(name, "+++ term matched to sync point " + i + ", matching took " + (System.currentTimeMillis() - begin) + "ms");
                            continue loop;
                        }
                    }

                    debug(name, "!!! term not matched to any sync point, matching took " + (System.currentTimeMillis() - begin) + "ms");
                    nextQueue.add(next);
                }
            }

            /* swap the queues */
            java.util.List<ConstrainedTerm> temp;
            temp = queue;
            queue = nextQueue;
            nextQueue = temp;
            nextQueue.clear();
        }

        return nextSyncNodes;
    }

    public static boolean matchSyncNode(
            int i,
            SyncNode ct1,
            SyncNode ct2,
            java.util.List<ConjunctiveFormula> startEnsures,
            java.util.List<ConjunctiveFormula> targetEnsures) {
        debug("??? do they match");
        trace("    - [llvm] " + ct1.currSyncNode.toString());
        trace("             constraint: " + ct1.constraint.toString());
        trace("    - [vx86] " + ct2.currSyncNode.toString());
        trace("             constraint: " + ct2.constraint.toString());
        trace("    - [vars] " + startEnsures.get(ct1.startSyncPoint).toString());
        trace("          => " + targetEnsures.get(i).toString());

        // starting constraints implies target constraints
        ConjunctiveFormula c1 = ConjunctiveFormula.of(ct1.constraint);
        ConjunctiveFormula c2 = ConjunctiveFormula.of(ct2.constraint);
        ConjunctiveFormula c0 = ConjunctiveFormula.of(startEnsures.get(ct1.startSyncPoint));
        ConjunctiveFormula e = ConjunctiveFormula.of(targetEnsures.get(i));
        ConjunctiveFormula c = c1.add(c2).add(c0).simplify(); // TODO: termContext ??

        Boolean check1 = null;
        Boolean check2 = null;
        Boolean check3 = null;

        long begin = System.currentTimeMillis();

        if (!(check1 = c.isFalse()) &&
                // use the same timeout as implication to avoid incorrect matches
                !(check2 = c.checkUnsatWithTimeout(new FormulaContext(FormulaContext.Kind.EquivConstr, null, c.globalContext()),
                                                    c.globalContext().constraintOps.smtOptions.z3ImplTimeout))
                && (check3 = c.smartImplies(e))) {
            long elapsed = System.currentTimeMillis() - begin;

            // these two synchronization nodes match
            // a synchronization point
            ct1.mark = Mark.BLACK;
            ct2.mark = Mark.BLACK;

            debug("    !!! YES took " + elapsed + "ms");
            return true;
        } else {
            long elapsed = System.currentTimeMillis() - begin;

            debug("    !!! NO took " + elapsed + "ms");
            smt("    c (unsat: " + check1 + ") = " + c.toStringMultiline());
            smt("    ####################");
            smt("    e = " + e.toStringMultiline());
            smt("    ####################");
            smt("    c in smt (unsat: " + check2 + ") = " + KILtoSMTLib.translateConstraint(c).toString());
            smt("    ####################");
            return false;
        }
    }

    public static boolean isAllMatched(
            int i,
            java.util.List<Set<SyncNode>> syncNodes1,
            java.util.List<Set<SyncNode>> syncNodes2) {
        for (SyncNode ct1 : syncNodes1.get(i)) {
            if (ct1.mark != Mark.BLACK) {
                return false;
            }
        }

        for (SyncNode ct2 : syncNodes2.get(i)) {
            if (ct2.mark != Mark.BLACK) {
                return false;
            }
        }

        return true;
    }

    public static void matchSyncNodes(
            java.util.List<Set<SyncNode>> syncNodes1,
            java.util.List<Set<SyncNode>> syncNodes2,
            java.util.List<ConjunctiveFormula> startEnsures,
            java.util.List<ConjunctiveFormula> targetEnsures) {

        assert startEnsures.size() == targetEnsures.size();
        assert syncNodes1.size() == targetEnsures.size();
        assert syncNodes2.size() == targetEnsures.size();

        int numSyncPoints = targetEnsures.size();

        for (int i = 0; i < numSyncPoints; i++) {
            debug("########################## matching nodes in sync point bucket " + i +
                    " with (" + syncNodes1.get(i).size() + ", " + syncNodes2.get(i).size() + ")");

            List<SyncNode> remaining1 = new ArrayList<SyncNode>();
            List<SyncNode> remaining2 = new ArrayList<SyncNode>();

            outer: for (SyncNode ct1 : syncNodes1.get(i)) {
                for (SyncNode ct2 : syncNodes2.get(i)) {
                    if (ct1.startSyncPoint != ct2.startSyncPoint) continue;
                    if (ct1.mark == Mark.BLACK && ct2.mark == Mark.BLACK) continue;

                    // since it's less likely for two sync nodes to match
                    // one at this point, this is just a heuristic to reduce
                    // the number of z3 queries required
                    if (ct1.mark == Mark.BLACK || ct2.mark == Mark.BLACK) {
                        remaining1.add(ct1);
                        remaining2.add(ct2);
                        continue;
                    }

                    boolean matched = matchSyncNode(i, ct1, ct2, startEnsures, targetEnsures);

                    if (matched && isAllMatched(i, syncNodes1, syncNodes2)) {
                        // if matching status changed and all have been matched
                        // break the loop now
                        break outer;
                    }
                }
            }

            if (!isAllMatched(i, syncNodes1, syncNodes2)) {
                for (int j = 0; j < remaining1.size(); j++) {
                    matchSyncNode(i, remaining1.get(j), remaining2.get(j), startEnsures, targetEnsures);
                }
            }
        }
    }

    public static void validateSyncNodes(java.util.List<Set<SyncNode>> syncNodes) {
        // TODO: implement more efficiently

        // mark grey for invalid nodes
        boolean changed = true;
        while (changed) {
            changed = false;
            for (Set<SyncNode> ssn : syncNodes) {
                for (SyncNode sn : ssn) {
                    if (sn.prevSyncNode.mark == Mark.BLACK || sn.prevSyncNode.mark == Mark.GREY) {
                        switch (sn.mark) {
                        case BLACK:
                            assert false; // TODO: what happend?
                            break;
                        case RED:
                            sn.mark = Mark.GREY;
                            changed = true;
                            break;
                        case GREY:
                            break;
                        }
                    }
                }
            }
        }

        // sweep grey nodes
        for (int i = 0; i < syncNodes.size(); i++) {
            Set<SyncNode> set = syncNodes.get(i).stream()
                    .filter(n -> n.mark != Mark.GREY)
                    .collect(Collectors.toSet());
            syncNodes.set(i, set);
        }
    }

    public static java.util.List<Set<SyncNode>> newListOfSets(int size) {
        java.util.List<Set<SyncNode>> list = new ArrayList<>();
        for (int i = 0; i < size; i++) {
            list.add(new HashSet<SyncNode>());
        }
        return list;
    }

    public static java.util.List<Set<SyncNode>> mergeListOfSets(
            java.util.List<Set<SyncNode>> to,
            java.util.List<Set<SyncNode>> from
    ) {
        assert to.size() == from.size();
        for (int i = 0; i < to.size(); i++) {
            to.get(i).addAll(from.get(i));
        }
        return to;
    }

    private static class SyncNode {
        public int startSyncPoint;
        public SyncNode prevSyncNode;
        public ConstrainedTerm currSyncNode;
        public ConjunctiveFormula constraint;
        public Mark mark;

        public SyncNode(
                int startSyncPoint,
                SyncNode prevSyncNode,
                ConstrainedTerm currSyncNode,
                ConjunctiveFormula constraint
        ) {
            this.startSyncPoint = startSyncPoint;
            this.prevSyncNode = prevSyncNode;
            this.currSyncNode = currSyncNode;
            this.constraint = constraint;
            this.mark = Mark.RED;
        }
    }

    private enum Mark {
        RED,    // not matched yet
        BLACK,  // matched
        GREY    // invalid; its parent was matched later
    }


}
