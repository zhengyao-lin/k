// Copyright (c) 2013-2019 K Team. All Rights Reserved.
package org.kframework.backend.java.util;

import com.google.common.collect.ImmutableSet;
import org.apache.commons.collections4.map.HashedMap;
import org.apache.commons.io.IOUtils;
import org.kframework.backend.java.kil.GlobalContext;
import org.kframework.backend.java.symbolic.EquivChecker;
import org.kframework.backend.java.symbolic.JavaExecutionOptions;
import org.kframework.backend.java.z3.Z3Context;
import org.kframework.backend.java.z3.Z3Exception;
import org.kframework.backend.java.z3.Z3Params;
import org.kframework.backend.java.z3.Z3Solver;
import org.kframework.backend.java.z3.Z3Status;
import org.kframework.builtin.Sorts;
import org.kframework.utils.OS;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.options.SMTOptions;

import java.io.IOException;
import java.io.PrintWriter;
import java.util.*;
import java.util.concurrent.TimeUnit;

import static org.kframework.kore.KORE.*;

/**
 * @author Traian
 */
public class Z3Wrapper {

    public static final Set<String> Z3_QUERY_RESULTS = ImmutableSet.of("unknown", "sat", "unsat");

    public String CHECK_SAT;

    public Map<String, List<String>> smtPreludeMap;
    public String preludeMode = "default";

    public final SMTOptions options;
    private final JavaExecutionOptions javaExecutionOptions;
    private final KExceptionManager kem;
    private final FileUtil files;
    private final StateLog stateLog;
    private final GlobalContext global;

    public Z3Wrapper(
            SMTOptions options,
            KExceptionManager kem,
            JavaExecutionOptions javaExecutionOptions,
            FileUtil files,
            StateLog stateLog, GlobalContext globalContext) {
        this.options = options;
        this.kem = kem;
        this.javaExecutionOptions = javaExecutionOptions;
        this.files = files;
        this.stateLog = stateLog;
        this.global = globalContext;

        String defaultPrelude = ""
                + "(set-option :auto-config false)\n"
                + "(set-option :smt.mbqi false)\n";

        if (options.smtPreludeMap == null) {
            smtPreludeMap = new HashedMap<String, List<String>>() {{
                put("default", new ArrayList<String>(Arrays.asList(defaultPrelude)));
            }};
        } else {
            String[] items = options.smtPreludeMap.split(";");
            smtPreludeMap = new HashedMap<String, List<String>>();
            for (String item : items) {
                String[] kv = item.split(":");
                if (kv.length == 1) {
                    smtPreludeMap = new HashedMap<String, List<String>>() {{
                        put("default", new ArrayList<String>(Arrays.asList(defaultPrelude)));
                    }};
                    break;
                } else if (kv.length == 2) {
                    String[] prelude_paths = kv[1].split(",");
                    List<String> preludes = new ArrayList<String>();
                    for (String prelude_path : prelude_paths) {
                        preludes.add(files.loadFromWorkingDirectory(prelude_path));
                    }
                    smtPreludeMap.put(kv[0], preludes);
                } else {
                    assert false;
                }
            }
        }
        CHECK_SAT = options.z3Tactic == null ? "(check-sat)" : "(check-sat-using " + options.z3Tactic + ")";
    }

    public boolean isUnsat(CharSequence query, int timeout, Z3Profiler timer) {
        // stateLog.log(StateLog.LogEvent.Z3QUERY,
        //         KToken(SMT_PRELUDE + "\n" + query + "\n" + CHECK_SAT + "\n", Sorts.Z3Query()));
        if (options.z3JNI) {
            return checkQueryWithLibrary(query, timeout);
        } else {
            return checkQueryWithExternalProcess(query, timeout, timer);
        }
    }

    private String getDefaultPrelude() {
        return smtPreludeMap.getOrDefault(preludeMode, smtPreludeMap.get("default")).get(0);
    }

    private boolean checkQueryWithLibrary(CharSequence query, int timeout) {
        boolean result = false;
        try (Z3Context context = new Z3Context()) {
            Z3Solver solver = new Z3Solver(context);
            Z3Params params = new Z3Params(context);
            params.add("timeout", timeout);
            solver.setParams(params);
            solver._assert(context.parseSmtlib2(getDefaultPrelude() + query));
            result = solver.check() == Z3Status.UNSAT;
        } catch (Z3Exception e) {
            kem.registerCriticalWarning(
                    "failed to translate smtlib expression:\n" + getDefaultPrelude() + query, e);
        } catch (UnsatisfiedLinkError e) {
            System.err.println(System.getProperty("java.library.path"));
            throw e;
        }
        return result;
    }

    private ProcessBuilder getProcessBuilder(int timeout, int seed) {
        ProcessBuilder pb;
        if (timeout > 0) {
            pb = files.getProcessBuilder().command(
                    OS.current().getNativeExecutable("z3"),
                    "-in",
                    "-smt2",
                    "-t:" + timeout,
                    "smt.random_seed=" + seed);
        } else {
            pb = files.getProcessBuilder().command(
                    OS.current().getNativeExecutable("z3"),
                    "-in",
                    "-smt2",
                    "smt.random_seed=" + seed);
        }
        pb.redirectInput(ProcessBuilder.Redirect.PIPE);
        pb.redirectOutput(ProcessBuilder.Redirect.PIPE);
        return pb;
    }

    /**
     * @return true if query result is unsat, false otherwise.
     */
    private boolean checkQueryWithExternalProcessAndPrelude(CharSequence query, int timeout, Z3Profiler profiler, String prelude) {
        String result = "";
        // profiler.startQuery();
        try {
            // profiler.startRun();
            long begin = System.currentTimeMillis();

            ProcessBuilder[] builders = new ProcessBuilder[options.z3Par];
            Process[] procs = new Process[options.z3Par];

            EquivChecker.debug("spawning " + options.z3Par + " process(es) for z3");

            for (int i = 0; i < options.z3Par; i++) {
                builders[i] = getProcessBuilder(timeout, i);
                EquivChecker.debug(" > z3 process " + i + ": " + String.join(" ", builders[i].command()));
                procs[i] = builders[i].start();
                PrintWriter input = new PrintWriter(procs[i].getOutputStream());
                input.format("%s%s%s\n", prelude, query, CHECK_SAT);
                input.close();
            }

            // When the process dies, that input stream does not go away automatically.
            // https://stackoverflow.com/a/7100172/4182868

            ProcessBuilder succeededBuilder;

            outer: while (true) {
                for (int i = 0; i < options.z3Par; i++) {
                    if (procs[i].waitFor(10, TimeUnit.MILLISECONDS)) {
                        EquivChecker.debug(" > process " + i + " ended first");
                        result = IOUtils.toString(procs[i].getInputStream()).trim();
                        succeededBuilder = builders[i];
                        for (int j = 0; j < options.z3Par; j++) {
                            procs[j].destroy();
                        }
                        break outer;
                    }
                }
            }

            long elapsed = System.currentTimeMillis() - begin;
            // profiler.endRun(timeout);

            if (result.isEmpty()) {
                result = "Z3 error: ended with no output";
            }

            EquivChecker.addAccumulatedZ3Time(elapsed);
            EquivChecker.saveZ3Result(prelude, query.toString(), result, elapsed, succeededBuilder);

            if (timeout > 0 && elapsed > timeout) {
                EquivChecker.debug("z3 query likely timed out");
                EquivChecker.trace(query.toString());
            }
        } catch (Exception e) {
            throw KEMException.criticalError("Exception while invoking Z3", e);
        } finally {
            // if (javaExecutionOptions.debugZ3 && profiler.isLastRunTimeout()) {
                //In case of timeout, result is "unknown", so evaluation can proceed.
                // global.log().format("\nZ3 likely timeout\n");
            // }
        }
        // stateLog.log(StateLog.LogEvent.Z3RESULT, KToken(result, Sorts.Z3Result()));
        if (!Z3_QUERY_RESULTS.contains(result)) {
            throw KEMException.criticalError("Z3 crashed on input query:\n" + query + "\nresult:\n" + result);
        }
        if (javaExecutionOptions.debugZ3) {
            global.log().format("\nZ3 query result: %s\n", result);
        }
        // profiler.queryResult(result);
        return "unsat".equals(result);
    }

    private boolean checkQueryWithExternalProcess(CharSequence query, int timeout, Z3Profiler profiler) {
        // TODO: hacky
        for (String prelude : smtPreludeMap.getOrDefault(preludeMode, smtPreludeMap.get("default"))) {
            // TODO: we are assuming the sequence of preludes we have: T1, T2, ...
            // are such that T1 is contained in T2, T2 is contained in T3 etc.
            // so that if a query is unsat in Ti, then it has to be unsat in all of Tj's for j >= i
            if (checkQueryWithExternalProcessAndPrelude(query, timeout, profiler, prelude)) {
                return true;
            }
        }
        return false;
    }
}
