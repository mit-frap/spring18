Problem Sets for MIT 6.822 Formal Reasoning About Programs (Spring 2018)
========================================================================

Instructions for completing problem set #X
------------------------------------------

1. Run `make` in the directory `psetX/`.
2. Read the module signature for the problem set in the file
   `psetX/PsetXSig.v`. These are the instructions!
3. Complete `psetX/PsetX.v`, which implements the module signature
   in `psetX/PsetXSig.v`. In your complete `PsetX.v`, there should be no
   uses of `Admitted` or `admit` (or similar holes).
4. Run `make` in the `psetX/` directory and ensure it builds without error.
5. Upload your `psetX/PsetX.v` file to the
   [class website](https://frap.csail.mit.edu/Private/student).

Tips for building problem sets
------------------------------

### Setting PATH for coqc

```
$ PATH=(your bin directory where coqc resides):$PATH
$ export PATH
```

- Where is my bin directory?
  + CoqIDE users
    * CoqIDE bundle already includes binaries, so we can use them.
    * Windows: the directory where `coqide.exe` is located. Make sure `coqc.exe` is also in there.
    * Mac: `(Your CoqIDE app path)/Contents/Resources/bin`
  + Users who installed Coq with Homebrew
    * The typical path is `/usr/local/bin`, but it may differ by Homebrew configuration.
  + All other users who manually installed Coq: just the location you gave during `./configure`
- I recommend to embed above commands in your `~/.bashrc` or `~/.zshrc`.

### Building problem sets

```
$ source configure_coqbin.sh # optional
$ git submodule init
$ git submodule update
$ make -C frap lib
$ make -C pset1
```

- Above procedure assumes PATH is set for detecting `coqc` (check with `which coqc`!).
- You should execute `configure_coqbin.sh` with `source` (or just `.`) in order to export the variable to the parent process.
- If you already set the COQBIN variable, you don't need to execute the script.
