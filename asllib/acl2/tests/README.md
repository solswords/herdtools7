
Running a test with ACL2's ASL interpreter
=======================

Build aslref as described in the "Source build" section of herdtools7/INSTALL.md.

Dump the static environment and AST for an ASL program into a Lisp object file using:
```
   aslref --print-lisp --no-exec myprogram.asl > myprogram-ast.lsp
```

Run ACL2 and submit the form:
```
    (assign :fname "myprogram-ast.lsp")
    (ld "run-test.lsp")
```

Caveats: Currently runtest.lsp only interprets the "main" function of the program; it
doesn't initialize global variables.

The result is a list containing the return value from "main" if successful, or an error if
the code produced an error or uncaught exception.
