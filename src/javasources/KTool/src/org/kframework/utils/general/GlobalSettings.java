// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.utils.general;

import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.kframework.utils.file.KPaths;

import java.io.File;

public class GlobalSettings {

    public static File getNativeExecutable(String executable) {
        File f = null;
        String basePath = KPaths.getKBase(false);

        switch (GlobalSettings.os()) {
            case UNIX:
                f = new File(basePath + "/lib/native/linux/" + executable);
                f.setExecutable(true, false);
                break;
            case WIN:
                f = new File(basePath + "/lib/native/cygwin/" + executable + ".exe");
                break;
            case OSX:
                f = new File(basePath + "/lib/native/macosx/" + executable);
                f.setExecutable(true, false);
                break;
            default:
                GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.INTERNAL, 
                        "Unknown OS type. " + System.getProperty("os.name") + " not recognized. " +
                        "Please contact K developers with details of your OS."));
        }

        return f;
    }

    public enum OS {
        OSX, UNIX, UNKNOWN, WIN
    }

    private static OS os = null;;
    public static KExceptionManager kem;
    // this is used by kast to know what parser to use fort the input string
    public static ParserType whatParser = ParserType.PROGRAM;
    
    public static OS os() {
        if (os == null) {
            String osString = System.getProperty("os.name").toLowerCase();
            if (osString.contains("nix") || osString.contains("nux")) os = OS.UNIX;
            else if (osString.contains("win")) os = OS.WIN;
            else if (osString.contains("mac")) os = OS.OSX;
            else os = OS.UNKNOWN;
        }
        return os;
    }

    public static boolean isWindowsOS() {
        return os() == OS.WIN;
    }

    public static boolean isPosix() {
        return os() == OS.UNIX || os() == OS.OSX;
    }

    public enum ParserType {
        PROGRAM, GROUND, RULES, BINARY, NEWPROGRAM
    }
    
    public static String CHECK;
}
