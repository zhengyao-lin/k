// Copyright (c) 2016-2019 K Team. All Rights Reserved.

package org.kframework.backend.java.symbolic;

import org.kframework.backend.java.builtins.BoolToken;
import org.kframework.backend.java.kil.*;
import org.kframework.backend.java.util.FormulaContext;
import org.kframework.definition.Module;
import org.kframework.keq.KEqFrontEnd;
import org.kframework.keq.KEqOptions;
import org.kframework.kompile.CompiledDefinition;
import org.kframework.kore.K;
import org.kframework.kore.KLabel;
import org.kframework.unparser.ColorSetting;
import org.kframework.unparser.OutputModes;
import org.kframework.utils.file.FileUtil;
import scala.Tuple2;

import java.io.File;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.nio.file.attribute.PosixFilePermission;
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
    public static void smt(String msg) { if (KEqFrontEnd.globalKEqOptions != null && KEqFrontEnd.globalKEqOptions.showSMT) System.out.println(msg); }
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

    public synchronized static void saveZ3Result(String prelude, String query, String result, long time, ProcessBuilder proc) {
        if (KEqFrontEnd.globalKEqOptions != null && KEqFrontEnd.globalKEqOptions.z3QueryLogDir != null) {
            try {
                if (current_query_dir == null) {
                    File dir = new File(KEqFrontEnd.globalKEqOptions.z3QueryLogDir);

                    // rwxr-xr-x
                    Set<PosixFilePermission> permissions = new HashSet<>();
                    permissions.add(PosixFilePermission.OWNER_READ);
                    permissions.add(PosixFilePermission.OWNER_WRITE);
                    permissions.add(PosixFilePermission.OWNER_EXECUTE);
                    permissions.add(PosixFilePermission.GROUP_READ);
                    permissions.add(PosixFilePermission.GROUP_EXECUTE);
                    permissions.add(PosixFilePermission.OTHERS_READ);
                    permissions.add(PosixFilePermission.OTHERS_EXECUTE);

                    if (!dir.exists()) {
                        dir.mkdir();
                        Files.setPosixFilePermissions(dir.toPath(), permissions);
                    }

                    Path path = Files.createTempDirectory(Paths.get(dir.getPath()), "z3-query-");
                    current_query_dir = path.toFile();
                    Files.setPosixFilePermissions(path, permissions);

                    System.out.println("storing z3 queries to " + current_query_dir.getAbsolutePath());
                }

                String command = String.join(" ", proc.command());

                debug("smt query " + current_query_dir + "/q-" + query_counter + ".smt made, result: " + result + ", took " + time + "ms");

                File log = new File(current_query_dir, "q-" + query_counter + ".smt");
                log.createNewFile();

                // rw-rw-rw-
                Set<PosixFilePermission> permissions = new HashSet<>();
                permissions.add(PosixFilePermission.OWNER_READ);
                permissions.add(PosixFilePermission.OWNER_WRITE);
                permissions.add(PosixFilePermission.GROUP_READ);
                permissions.add(PosixFilePermission.GROUP_WRITE);
                permissions.add(PosixFilePermission.OTHERS_READ);
                permissions.add(PosixFilePermission.OTHERS_WRITE);
                Files.setPosixFilePermissions(log.toPath(), permissions);

                FileWriter writer = new FileWriter(log);
                writer.write("; " + command + "\n\n");
                writer.write(prelude + "\n");
                writer.write(query + "\n\n(check-sat)\n");
                writer.write("; " + result + ", took " + time + "ms\n");
                writer.close();

                query_counter += 1;
            } catch (IOException exc) {
                System.err.println(exc.toString());
                exc.printStackTrace(System.err);
            }
        }
    }

    private static long accumulatedZ3Time = 0;

    public static synchronized void addAccumulatedZ3Time(long ms) {
        accumulatedZ3Time += ms;
    }

    private static GlobalContext global;

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

        // do a full gc before starting the symbolic rewriting
        Runtime.getRuntime().gc();

        int numSyncPoints = targetEnsures.size();

        global = startSyncNodes1.get(0).termContext().global();
        String matchingPrelude =
                KEqFrontEnd.globalKEqOptions.matchingPrelude == null
                        ? "" : global.files.loadFromWorkingDirectory(KEqFrontEnd.globalKEqOptions.matchingPrelude);

        /**
         * This is a map from:
         *   initial sync point number => set of sync nodes rewritten from an instance of that sync points
         */
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

            currSyncNodes1.add(new SyncNode(i, i, null, t1, null)); // TODO: check if null is safe
            currSyncNodes2.add(new SyncNode(i, i, null, t2, null));
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

                try {
                    t1.join();
                } catch (InterruptedException e) {
                    debug("t1 interrupted " + e.toString());
                }

                try {
                    t2.join();
                } catch (InterruptedException e) {
                    debug("t2 interrupted " + e.toString());
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

            // TODO: H A C K Y !!!
            // global.constraintOps.z3.preludeMode = "matching";

            // global.constraintOps.z3.options.z3Par *= KEqFrontEnd.globalKEqOptions.parallel;
            // ^ increase the number of z3 processes since matching queries are
            // usually very costly

            matchSyncNodes(allSyncNodes1, allSyncNodes2, startEnsures, targetEnsures);

            // global.constraintOps.z3.preludeMode = "default";
            // global.constraintOps.z3.options.z3Par /= KEqFrontEnd.globalKEqOptions.parallel;

            // validateSyncNodes(allSyncNodes1);
            // validateSyncNodes(allSyncNodes2);

            elapsed = System.currentTimeMillis() - matchingBegin;

            debug("### end of matching:");
            debug("  - matching total: " + (((double)elapsed) / 1000.0) + "s");
            debug("  - z3 total query time: " + (((double)accumulatedZ3Time) / 1000.0) + "s");

            currSyncNodes1.clear();
            currSyncNodes2.clear();

            for (int i = 0; i < numSyncPoints; i++) {
                for (SyncNode node : allSyncNodes1.get(i)) {
                    // ignore error terms in llvm
                    if (node.mark == Mark.RED && !isErrorTerm(node.currSyncNode)) {
                        debug("[llvm] found a remaining state rewritten from sync point " + i);
                        trace(" - constrained term: " + node.currSyncNode.toString());
                        currSyncNodes1.add(node);
                    }
                }
                for (SyncNode node : allSyncNodes2.get(i)) {
                    if (node.mark == Mark.RED) {
                        debug("[x86] found a remaining state rewritten from sync point " + i);
                        trace(" - constrained term: " + node.currSyncNode.toString());
                        currSyncNodes2.add(node);
                    }
                }
            }

            if (currSyncNodes1.isEmpty() != currSyncNodes2.isEmpty()) {
                return false; // TODO: output more information for failure
            }

            if (!currSyncNodes1.isEmpty() && !currSyncNodes2.isEmpty()) {
                debug("second round of matching is not possible in the current semantics");
                assert false;
            }
        }

        return true;
    }

    /**
     * Get the set of all sync nodes from a list of sync nodes matched to different sync points
     */
    public static java.util.List<Set<SyncNode>> getNextSyncNodes(
            String name,
            java.util.List<SyncNode> currSyncNodes,
            java.util.List<ConstrainedTerm> targetSyncNodes,
            SymbolicRewriter rewriter
    ) {
        int numSyncPoints = targetSyncNodes.size();
        java.util.List<Set<SyncNode>> nextSyncNodes = newListOfSets(numSyncPoints);
        for (SyncNode currSyncNode : currSyncNodes) {
            Set<SyncNode> nodes = getNextSyncNodes(name, currSyncNode, targetSyncNodes, rewriter);
            if (nodes == null) return null; // failed // TODO: output more information for failure
            nextSyncNodes.get(currSyncNode.matchedSyncPoint).addAll(nodes);
        }
        return nextSyncNodes;
    }

    /**
     * Same but only computes next sync nodes for a single node
     */
    public static Set<SyncNode> getNextSyncNodes(
            String name,
            SyncNode currSyncNode,
            java.util.List<ConstrainedTerm> targetSyncNodes,
            SymbolicRewriter rewriter
    ) {
        int numSyncPoints = targetSyncNodes.size();

        Set<SyncNode> nextSyncNodes = new HashSet<SyncNode>();

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
                trace(name, ">>> from term: " + curr.toString());

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
                            SyncNode node = new SyncNode(currSyncNode.startSyncPoint, i, currSyncNode, next, constraint);
                            nextSyncNodes.add(node);
                            debug(name, "+++ term matched to sync point " + i +
                                    ", creating sync node " + System.identityHashCode(node) +
                                    ", matching took " + (System.currentTimeMillis() - begin) + "ms");
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

    public static boolean isErrorTerm(ConstrainedTerm ct) {
        if (KEqFrontEnd.globalKEqOptions.bisimultion) {
            return false;
        }

        try {
            KItem errorItem = (KItem)((BuiltinList)ct.term().getCellContentsByName("<k>").get(0)).get(0);
            String errorContent = ((KItem)errorItem.klist().items().get(0)).klabel().name();
            boolean isUndefined =
                    errorContent.startsWith("outOfBoundsMemoryAccess") ||
                    errorContent.startsWith("invalidMemoryOperation") ||
                    errorContent.startsWith("divisionByZero") ||
                    errorContent.startsWith("arithmeticOverflow");
            return errorItem.klabel().name().equals("error") && isUndefined;
        } catch (Exception e) {
            return false;
        }
    }

    // path conditions are the new constraints generated during the execution:  curr.constraint - prev.constraint
    public static ConjunctiveFormula getPathCondition(SyncNode node) {
        return ((ConjunctiveFormula)node.prevSyncNode.currSyncNode.constraint()
                .evaluate(node.prevSyncNode.currSyncNode.termContext()))
                .simplifyConstraint(node.currSyncNode.constraint());
    }

    // NOTE: this function is NOT thread safe
    public static boolean matchSyncNode(
            int i,
            SyncNode ct1,
            SyncNode ct2,
            java.util.List<ConjunctiveFormula> startEnsures,
            java.util.List<ConjunctiveFormula> targetEnsures,
            Set<SyncNode> allSyncNodes1,
            Set<SyncNode> allSyncNodes2
            ) {
        debug(">>> matching terms " + System.identityHashCode(ct1) + " and " + System.identityHashCode(ct2));
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

        long begin = System.currentTimeMillis();

        global.constraintOps.z3.preludeMode = "matching";

        // a preliminary check to see if the concrete states of these
        // symbolic states are bisimilar (given that we don't lose any models
        // during the conjunction of constraints)
        boolean bisimilar =
                !c.isFalse() &&
                // use the same timeout as implication to avoid incorrect matches
                !c.checkUnsatWithTimeout(
                    new FormulaContext(
                        FormulaContext.Kind.EquivConstr,
                        null,
                        c.globalContext()
                    ),
                    c.globalContext().constraintOps.smtOptions.z3ImplTimeout
                );

        bisimilar = bisimilar && c.smartImplies(e);
        global.constraintOps.z3.preludeMode = "default";

        long elapsed = System.currentTimeMillis() - begin;

        if (bisimilar) {
            ct1.mark = Mark.BLACK;
            ct2.mark = Mark.BLACK;
            debug("    !!! YES took " + elapsed + "ms");
            return true;
        } else {
            debug("    !!! NO took " + elapsed + "ms");
            return false;
        }
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
            // if any of the resulting term is an error term for the left (llvm) semantics
            boolean leftHasErrorTerm = false;
            int numLeftErrorTerm = 0;
            int numRightErrorTerm = 0;

            for (SyncNode ct1 : syncNodes1.get(i)) {
                if (isErrorTerm(ct1.currSyncNode)) {
                    leftHasErrorTerm = true;
                    numLeftErrorTerm++;
                }
            }

            for (SyncNode ct2 : syncNodes2.get(i)) {
                if (isErrorTerm(ct2.currSyncNode)) {
                    numRightErrorTerm++;
                }
            }

            debug("########################## matching nodes rewritten from sync node " + i +
                    ": (" + syncNodes1.get(i).size() + " (" + numLeftErrorTerm + " error term(s)), " +
                            syncNodes2.get(i).size() + " (" + numRightErrorTerm + " error term(s)))");

            // vx86 major
            for (SyncNode ct2 : syncNodes2.get(i)) {
                // sync nodes from llvm that are not matched
                Set<SyncNode> notMatched = new HashSet<>();
                boolean ct2HasMatchedTerm = false;

                for (SyncNode ct1 : syncNodes1.get(i)) {
                    if (!isErrorTerm(ct1.currSyncNode)) {
                        notMatched.add(ct1);
                    }
                }

                // no need to match error terms in x86
                if (!isErrorTerm(ct2.currSyncNode)) {
                    debug(">>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>");
                    debug(">>> matching x86 term " + System.identityHashCode(ct2) + " against non-error llvm terms");
                    debug(">>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>");
                    for (SyncNode ct1 : syncNodes1.get(i)) {
                        assert ct1.startSyncPoint == ct2.startSyncPoint;
                        if (ct1.matchedSyncPoint != ct2.matchedSyncPoint) continue;
                        if (ct1.mark == Mark.BLACK && ct2.mark == Mark.BLACK) continue;

                        // ignore error terms in llvm
                        if (isErrorTerm(ct1.currSyncNode)) continue;

                        boolean matched = matchSyncNode(
                                ct2.matchedSyncPoint, ct1, ct2, startEnsures, targetEnsures,
                                syncNodes1.get(i), syncNodes2.get(i)
                        );

                        if (matched) {
                            notMatched.remove(ct1);
                            ct2HasMatchedTerm = true;
                        }
                    }
                } else {
                    // error terms are automatically matched unless
                    // there is no llvm error term or
                    // the check below for shared models fails
                    if (leftHasErrorTerm) {
                        debug(">>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>");
                        debug(">>> checking x86 error node " + System.identityHashCode(ct2));
                        debug(">>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>");
                        ct2.mark = Mark.BLACK;
                    } else {
                        debug(">>> no error terms in llvm but found potential errors in vx86");
                        continue;
                    }
                }

                // check for shared models
                // instead of checking path condition => lhs \/ error1 \/ error2 ...
                // check if for every one of the rest of the non-error states, sigma,
                // constraints /\ sigma is unsatisfiable

                boolean disjointFromUnmatchTerms = true;

                // this should work for both normal and error terms
                // for normal terms, we check if:
                //  - the conjunction of the constraints with any other non-matched and non-error terms is unsat
                // for error terms, we check if:
                //  - the conjunction of the constraints with any other non-error terms is unsat
                for (SyncNode ct1 : notMatched) {
                    // some other unmatched state
                    debug("    checking if the x86 node " + System.identityHashCode(ct2) +
                            " has shared model with node " + System.identityHashCode(ct1));
                    trace("    term: " + ct1.currSyncNode.toString());

                    ConjunctiveFormula notSubsumedFormula = ConjunctiveFormula.of(ct1.constraint)
                            .add(ConjunctiveFormula.of(ct2.constraint))
                            .add(ConjunctiveFormula.of(startEnsures.get(ct1.startSyncPoint)))
                            .simplify();

                    long begin = System.currentTimeMillis();
                    global.constraintOps.z3.preludeMode = "matching";
                    boolean notSubsumed =
                            !notSubsumedFormula.isFalse() &&
                            !notSubsumedFormula.checkUnsatWithTimeout(
                                new FormulaContext(FormulaContext.Kind.EquivConstr, null, notSubsumedFormula.globalContext()),
                                notSubsumedFormula.globalContext().constraintOps.smtOptions.z3ImplTimeout
                            );
                    global.constraintOps.z3.preludeMode = "default";
                    long elapsed = System.currentTimeMillis() - begin;

                    if (notSubsumed) {
                        // cannot prove no shared model, abort to ensure soundness
                        debug("    !!! unable to prove, took " + elapsed + "ms");
                        ct2.mark = Mark.RED;
                        disjointFromUnmatchTerms = false;
                    } else {
                        debug("    +++ no shared model, took " + elapsed + "ms");
                    }
                }

                if (!isErrorTerm(ct2.currSyncNode) &&
                        !ct2HasMatchedTerm &&
                        leftHasErrorTerm &&
                        disjointFromUnmatchTerms) {
                    // this implies that the current sync point is
                    // completely subsumed by one of the error terms
                    // so we should also allow this case
                    debug("!!! x86 node " + System.identityHashCode(ct2) + " is completely subsumed by llvm error terms");
                    ct2.mark = Mark.BLACK;
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
        public int matchedSyncPoint;
        public SyncNode prevSyncNode;
        public ConstrainedTerm currSyncNode;
        public ConjunctiveFormula constraint;
        public Mark mark;

        public SyncNode(
                int startSyncPoint,
                int matchedSyncPoint,
                SyncNode prevSyncNode,
                ConstrainedTerm currSyncNode,
                ConjunctiveFormula constraint
        ) {
            this.startSyncPoint = startSyncPoint;
            this.matchedSyncPoint = matchedSyncPoint;
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
