#lang scribble/doc
@(require scribble/manual
          scribble/eval
          scribble/basic
	  (planet cce/scheme:7)
	  racket/sandbox
	  (only-in unstable/scribble declare-exporting/this-package)
          (for-label (this-package-in smt-solve)
                     (this-package-in smt-interface)
                     (this-package-in dimacs)))

@(define dimacs-eval 
   (make-scribble-evaluator 'racket/base
		   #:requires (list "dimacs.rkt" "smt-solve.rkt")))


@title[#:tag "top"]{An SMT-solver for Racket}
@author[(author+email "Ian Johnson" "ianj@ccs.neu.edu")
        (author+email "Paul Stansifer" "pauls@ccs.neu.edu")]


This package contains an SMT-solver written using the DPLL(T) framework. 
Its mechanics include conflict-based learned with the first unique implication point heuristic, 
efficient unit resolution with the 2-literal watching heuristic,
and ``smart'' literal choice with the variable state independent, decaying sum heuristic (popularized by the CHAFF solver).
Soon to be implemented: clause forgetting with the Minisat policy, and random restarts with the Picosat policy.

@table-of-contents[]

@section{An SMT-solver for Racket}

@subsection{The SMT-Solver interface}
@declare-exporting/this-package[(smt-solve) ()]

Types are detailed below.
The main function of the SMT solver is 

@defproc[(smt-solve [cnf dimacscnf?]
                    [t-state any/c]
                    [strength strength?]
                    [choose-literal (SMT? . -> . Literal?)])
         (or/c sat-exn? unsat-exn?)]{
Which takes a CNF, initial T-State, initial Strength and possibly a choice function and returns
the result as a struct encapsulating the final SMT state.}

Derived interfaces are

@defproc[(smt-assign [cnf dimacscnf?]
                     [t-state any/c]
                     [strength strength?]
                     [choose-literal (SMT? . -> . Literal?)])
         (or/c 'UNSAT (listof exact-integer?))]{
Uses @racket[smt-solve] to return @racket['UNSAT] or the partial model in the form of all satisfied DimacsLits.}

@defproc[(smt-decide [cnf dimacscnf?]
                     [t-state any/c]
                     [strength strength?]
                     [choose-literal (SMT? . -> . Literal?)])
         (or/c 'UNSAT 'SAT)]{
Like @racket[smt-assign], but does not extract the final model.}

@defproc[(sat-solve [cnf dimacscnf?]
                    [choose-literal (SMT? . -> . Literal?)])
         (or/c sat-exn? unsat-exn?)]
@defproc[(sat-assign [cnf dimacscnf?]
                     [choose-literal (SMT? . -> . Literal?)])
         (or/c 'UNSAT (listof exact-integer?))]
@defproc[(sat-decide [cnf dimacscnf?]
                     [choose-literal (SMT? . -> . Literal?)])
         (or/c 'UNSAT 'SAT)]{
Like smt-x, but initially parameterizes by the trivial theory.}

@examples[#:eval dimacs-eval
 (sat-assign (list 5 5 '((-1 2) (-1 3) (-2 4) (-3 -4) (1 -3 5))))
 (sat-decide (list 5 5 '((-1 2) (-1 3) (-2 4) (-3 -4) (1 -3 5))))]


@subsection{The T-Solver interface}
@declare-exporting/this-package[(smt-interface) ()]

@defstruct[sat-exn ([smt SMT?])]
@defstruct[unsat-exn ([smt SMT?])]{
  The structs that are the result of @racket[smt-solve], which encapsulate the final state of the SMT solver.
}


This is a fully fledged DPLL(T) SMT solver, but there are so common theories implemented. 
To write a theory solver, you must maintain the following interfaces:

@itemlist[
  @item{
   Your theory solver may encapsulate its state into a value that will be passed between
   the SMT solver and the SAT solver. This is what is meant by the type T-State. 
   It is opaque to the SAT solver, but is maintained through interfacing calls. You may choose
   not to use this feature and use global state, using some dummy value like @racket[#f].}
  @item{
   Strength is a Natural or @racket[+inf.0]. You may use this to control eagerness of the T-Solver. 
   Currently there is no logic to modify strength in the SAT solver, so it is coarse-grained.
   The SMT solver takes an initial strength value.
   At a time the SAT solver has a model, it will call T-Consistent? with @racket[+inf.0] strength.
   This is paramount for completeness. If this is not what you want, you can change it in sat-solve.rkt
   at its only callsite.}
  @item{
   The SMT solver should be driven externally. We mean that the SAT solver only understands DimacsLits,
   so any atomic propositions your T-solver interprets should already be in the T-State. 
   This is why the SMT solver takes in initial T-State.}
  @item{
   You must use parameterize to set 
   @defthing[T-Satisfy
             (any/c exact-integer? . -> . any/c)]
   @defthing[T-Backjump
             (any/c exact-nonnegative-integer? . -> . any/c)]
   @defthing[T-Propagate
	     (any/c strength? exact-integer? . -> . any/c)]
   @defthing[T-Explain
	     (any/c strength? exact-integer? . -> . any/c)]
   @defthing[T-Consistent?
	     (any/c strength? . -> . (or/c boolean? (listof exact-integer?)))]{
   which are briefly summarized in smt-interface.rkt, and detailed in
   Nieuwenhuis & Oliveras: Abstract DPLL and Abstract DPLL modulo theories. They are exected to have the
   same signatures as their respective default values given below.}
   @defproc[(sat-satisfy [t-state any/c]
			  [lit exact-integer?])
            any/c]
   @defproc[(sat-backjump [t-state any/c]
                          [backjump-by-sats exact-nonnegative-integer?])
	    any/c]
   @defproc[(sat-propagate [t-state any/c]
			   [strength strength?]
			   [lit exact-integer?])
	    any/c]
   @defproc[(sat-explain [t-state any/c]
			 [strength strength?]
			 [lit exact-integer?])
	    any/c]
   @defproc[(sat-consistent? [t-state any/c]
			     [strength strength?])
	    (or/c boolean? (listof exact-integer?))]
   Where strength is    
   @defproc[(strength? [x any/c]) boolean?]
   Strength describes how eager a T-Solver should be. It can be a natural number to denote some amount of approximation,
    or @racket[+inf.0] to denote exhaustiveness/completeness.

Because the SAT-solver is unaware of which literals are theory-interpreted, 
T-Satisfy, T-Propagate and T-Explain must be able to make the distinction.}]

@section{Visible data-structures}
@declare-exporting/this-package[(dimacs) ()]

There are a few datatypes that are exposed through the SMT/T-Solver interface.

@defproc[(dimacscnf? [x any/c]) boolean?]{
  DIMACS CNF is a simple format for describing propositional formulae in conjunctive normal form.
  Here it is an s-expression containing first the variable count, then clause count, then the list of clauses.
  DIMACS literals are non-zero integers whose absolute value is less than or equal to the variable count.
  A clause is a list of DIMACS literals.
@examples[#:eval dimacs-eval
 (dimacscnf? (list 5 5 '((-1 2) (-1 3) (-2 4) (-3 -4) (1 -3 5))))]}

 @defthing[SMT? (any/c . -> . boolean?)]{
  Predicate for recognizing the internal representation of the SMT solver.}
 @defthing[Literal? (any/c . -> . boolean?)]{
  Predicate for recognizing the internal representation of a literal.}
                            
@section{Acknowledgments}
The package uses the DPLL(T) framework described in
@link["http://portal.acm.org/citation.cfm?id=1217856.1217859"]{Solving SAT and SAT Modulo Theories: From an abstract Davis--Putnam--Logemann--Loveland procedure to DPLL (T)} by R. Nieuwenhuis and A. Oliveras.

@index-section[]

@close-eval[dimacs-eval]