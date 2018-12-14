# CTL-based formalization of smart contracts

An extension of [scilla-coq](https://github.com/ilyasergey/scilla-coq/blob/master/Contracts/Crowdfunding.v) via a branching-time temporal model for smart contracts.  

## Building Instructions

### Requirements

* Coq 8.8.2
* [Mathematical Components 1.6.4 or 1.7.0](http://math-comp.github.io/math-comp/) (`ssreflect`)

Installation via [OPAM](https://opam.ocaml.org/doc/Install.html):

```
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-mathcomp-ssreflect
```
The following lines may be necessary to find the right Coq compiler before compiling on command line or opening emacs: 

```
export OPAMROOT=~/opam-coq.8.8.2
eval `opam config env`
```

### Building the project

```
make clean; make
```

## Project Structure

* `Contracts/Crowdfunding.v` - contains the syntax and semantics for CTL (computation tree logic), crowdfunding contract semantics and the statement of correctness properties
* `Core/Automata2.v` is obsolete for this version of the development, but kept inside as a reference to the original model. 
