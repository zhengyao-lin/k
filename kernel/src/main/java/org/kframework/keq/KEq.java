// Copyright (c) 2014-2019 K Team. All Rights Reserved.
package org.kframework.keq;

import org.kframework.compile.Backend;
import org.kframework.definition.Definition;
import org.kframework.definition.Module;
import org.kframework.kompile.CompiledDefinition;
import org.kframework.kprove.KProve;
import org.kframework.rewriter.Rewriter;
import org.kframework.utils.Stopwatch;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;
import scala.Tuple2;

import java.util.function.Function;

public class KEq {
    private final KExceptionManager kem;
    private final FileUtil files;
    private Stopwatch sw;

    public KEq(KExceptionManager kem, FileUtil files, Stopwatch sw) {
        this.kem = kem;
        this.files = files;
        this.sw = sw;
    }

    public int run(
            CompiledDefinition commonDef,
            CompiledDefinition def1,
            CompiledDefinition def2,
            KEqOptions keqOptions,
            Backend backend,
            Function<Definition, Rewriter> commonGen,
            Function<Definition, Rewriter> gen1,
            Function<Definition, Rewriter> gen2) {
        System.out.println("keq starts");

        Rewriter[] rewriters = new Rewriter[3];
        Module[] specs = new Module[2];

        Thread t0 = new Thread(() -> {
            rewriters[2] = commonGen.apply(commonDef.kompiledDefinition);
        });

        Thread t1 = new Thread(() -> {
            Tuple2<Definition, Module> compiled1 = KProve.getProofDefinition(files.resolveWorkingDirectory(keqOptions.spec1), keqOptions.defModule1, keqOptions.specModule1, def1, backend, files, kem, sw);
            rewriters[0] = gen1.apply(compiled1._1());
            specs[0] = compiled1._2();
        });

        Thread t2 = new Thread(() -> {
            Tuple2<Definition, Module> compiled2 = KProve.getProofDefinition(files.resolveWorkingDirectory(keqOptions.spec2), keqOptions.defModule2, keqOptions.specModule2, def2, backend, files, kem, sw);
            rewriters[1] = gen2.apply(compiled2._1());
            specs[1] = compiled2._2();
        });

        t0.start();
        t1.start();
        t2.start();

        while (true) {
            try {
                t0.join();
                break;
            } catch (InterruptedException e) {
            }
        }

        while (true) {
            try {
                t1.join();
                break;
            } catch (InterruptedException e) {
            }
        }

        while (true) {
            try {
                t2.join();
                break;
            } catch (InterruptedException e) {
            }
        }

        boolean isEquivalent = rewriters[2].equivalence(rewriters[0], rewriters[1], specs[0], specs[1]);

        System.out.println(isEquivalent ? "#True" : "#False");

        return isEquivalent ? 0 : 1;
    }
}
