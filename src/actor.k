/*
 * Important Syntactic Catogories in the Actor Lanaguage 
 * (and their notations in the paper)
 * - Variables            (X)
 * - Atoms                (At)
 *     t  : boolean atom
 *     nil: boolean atom
 *     N  : natural numbers
 * - Primitive operations (F)
 *     Operations on atoms  (G)
 *     Arithmetic operations
 *     isatom       : recognizer for atoms
 *     isnat        : recognizer for natural numbers
 *     ispr         : recognizer for pairs
 *     br           : brancing (arity 3)
 *     pr           : pairing
 *     first, second: getters
 *     newadr       : actor primitive
 *     initbeh      : actor primitive
 *     send         : actor primitive
 *     become       : actor primitive
 * - Expressions (E)
 * - Values      (V)
 * - Contexts    (C)
 *
 */

require "substitution.k"

module ACTOR-SYNTAX

  imports SUBSTITUTION

  syntax Atom ::= Int   /* Should be non-negative Int */
                | "t"
		| "nil"

  syntax Op   ::= "isatom"
                | "isnat"
		| "ispr"
		| "br"
		| "pr"
		| "fst"
		| "snd"
		| "newadr"
		| "initbeh"
		| "send"
		| "become"

  syntax Val  ::= Atom
                | Id
                | "\\" Id "." Exp [binder]
	        | pr(Val, Val)

  syntax Exp  ::= Atom
                | Id
	        | "\\" Id "." Exp [binder]
	        | app(Exp, Exp)
	        | Op "(" Exps ")"
  
  syntax Cxt  ::= Atom
                | Id
	        | "\\" Id "." Cxt [binder]
	        | app(Cxt, Cxt)
	        | Op "(" Exps ")"
	        | "*"

  syntax Op 

  syntax Exps ::= List{Exp, ","}


  /* Meta-level */
  syntax KVariable ::= Id
  syntax KResult   ::= Val

endmodule

module ACTOR

  imports ACTOR-SYNTAX

endmodule
