# Project

- need to have a `_CoqProject`

```sh
coq_makefile -f _CoqProject *.v -o Makefile

make Basics.vo
# or
make
# which is equivalent to
coqc -Q . LF Basics.v
```

If you're using VSCode with VSCoq, you need to open the `LF` folder to export the directory to Coq's `LoadPath`.
