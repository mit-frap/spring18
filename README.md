Problem Sets for MIT 6.887 Formal Reasoning About Programs
==========================================================

Simple instructions for all psets
---------------------------------

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
