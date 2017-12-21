# Actor Semantics in K

### Installing and Running

- Download [K](http://github.com/kframework/k). Pull from `master` and follow instructions for building K.
- Navigate to the `src` directory, and run the command `kompile actor.k`
- Navigate to the `test` directory.
- Run the command `./run-pretty.sh FILE` to view the output of a particular file.
- Run the command `./exec_all.sh` to run all files in the `test` directory.
- Run the command`./test_all.sh` to run all files in the `test` directory, and check output against `.out` files.

### Verification

- Navigate to the `verification` directory.
- Simple addition example can be run using the command
```
krun --debug --directory ../src --prove equality_spec.k --z3-executable dummy.actor
```
- More complicated examples are a work in progress.
