# EOPL in Haskell

 - [Essentials of Programming Languages](https://github.com/mwand/eopl3) 
 - Rewritten in [Haskell](https://www.haskell.org/)

### Preliminaries

 - [Introduction to Haskell](https://docs.google.com/presentation/d/1fhXvoLHFgYE4AOfdl4MD_Puk7Vbj-8eKqquTi7b0t9I/edit?usp=sharing)

 - [An overview of programming languages](https://docs.google.com/presentation/d/1IG6xe4I1ao00jfyn-JGGBOQx3sWKLbf67eODpfxEXN0/edit?usp=sharing)

### Chapter 1: [Inductive Sets of Data](https://docs.google.com/presentation/d/1enC8Pp3dACVOm9VIc1lbJkUWfmLzGdE0237Aj5bARqg/edit?usp=sharing)

 - Recursively defined data types


### Chapter 2: [Data Abstraction](https://docs.google.com/presentation/d/1-y8zQLRDkqOtClr6bLyMXvyBJIUbyScQJFfeH_D8rjk/edit?usp=sharing)

 - Environment (representation)

 - Abstract syntax and its representation


### Chapter 3: [Expressions](https://docs.google.com/presentation/d/1ZU9TEcEN9BEZoBmavD_Ivvt39TXUnbsXqZHdJBvba1k/edit?usp=sharing)

 - LET: A expression language with local bindings

 - PROC: A language with procedures (based on LET)

 - LETREC: A language with recursive procedures (based on PROC)


### Chapter 4: [States](https://docs.google.com/presentation/d/1ZxFuia-KHExNJlXJXR7iEMQ_P7gVmAweVIVglJM7Ytg/edit?usp=sharing)

 - EXPLICIT-REFS: A language with explicit references (based on LETREC)

 - IMPLICIT-REFS: A language with implicit references (based on LETREC)

### Chapter 5: [Continuation-passing interpreters(LETREC-CPS,EXCEPTIONS)](https://docs.google.com/presentation/d/1I2Wl277VQRH2h8n-jc1W8IHnXNL5d_pzILJI07eRI6Y/edit?usp=sharing)

 - LETREC-CPS: Reimplement LETREC with a continuation-based interpreter (based on LETREC)

 - EXCEPTIONS: A language with exception handling (based on LETREC-CPS)

 - [THREADS: A multi-threaded concurrent language (based on LETRE-CPS and IMPLICIT-REFS)](https://docs.google.com/presentation/d/1d2jd_NtCxMdSEZTJI5M9kNz2QVk11cea-d86fnTo9zk/edit?usp=sharing)

### Chapter 7: Types

 - [CHECKED: A type-checked language (based on LETREC)](https://docs.google.com/presentation/d/1Jl8IkUpaIn5Mtmd6kKeSiBLpvWwO6RjMoMq4brT8Oc8/edit?usp=sharing)
 - [INFERRED: A language with type inference (based on CHECKED)](https://docs.google.com/presentation/d/1etasdRLpqwFuAAP117hdHzrZxeYibe3o8TJ6Px4HSlA/edit?usp=sharing)

### Chapter 8: Modules

 - [SIMPLE-MODULES: A modular language (based on CHECKED)](https://docs.google.com/presentation/d/1__dfiyEu3NSFawXhrNiHJv0ilB6lBDAN_CYjtVgt7Q0/edit?usp=sharing)
 - [OPAQUE-TYPES: A modular language with interfaces, i.e., module types (based on SIMPLE-MODULES)](https://docs.google.com/presentation/d/1SyUOEjuTCI1jRPhETEBtWbEWTCSaUVM15MVKaYJVUhQ/edit?usp=sharing)
 - [PROC-MODULES: A modular language with parameterized modules (based on OPAQUE-TYPES)](https://docs.google.com/presentation/d/1smr-YmaWr1YLof-biZ2VtHUiEZetuRHpiHLBgQGKkJk/edit?usp=sharing)

### Chapter 9: Objects and Classes (CLASSES)

 - CLASSES: An untyped object-oriented language (based on IMPLICIT-REFS)
 - TYPED-OO: A typed object-oriented language (based on CLASSES)

