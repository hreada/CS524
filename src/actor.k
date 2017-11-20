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

  syntax Val  ::= Atom
                | Id
                | "\\" Id "." Exp [binder]
	        | pr(Val, Val)

  /* Primitive operations */
  syntax Exp  ::= Val
                | "rec"     "(" Exp                 ")"
	        | "app"     "(" Exp "," Exp         ")"
                | "isatom"  "(" Exp                 ")"
                | "isnat"   "(" Exp                 ")"
                | "ispr"    "(" Exp                 ")" 
                | "br"      "(" Exp "," Exp "," Exp ")" [strict(1)]
                | "pr"      "(" Exp "," Exp         ")" 
                | "fst"     "(" Exp                 ")" 
                | "snd"     "(" Exp                 ")" 
                | "newadr"  "("                     ")" 
                | "initbeh" "(" Exp "," Exp         ")" 
                | "send"    "(" Exp "," Exp         ")" 
                | "become"  "(" Exp                 ")" 

  /* Non-primitive operations */
  syntax Exp  ::= "if" "(" Exp "," Exp "," Exp ")"
                | "let" "{" BindingExp "}" Exp
                | "seq" "(" Exp "," Exp ")"
                | "letactor" "{" BindingExps "}" Exp

  /* Binding expressions */
  syntax BindingExp  ::= Id ":=" Exp
  syntax BindingExps ::= List{BindingExp, ","}

  /* Meta-level */
  syntax KVariable ::= Id
  syntax KResult   ::= Val

endmodule

module ACTOR

  imports ACTOR-SYNTAX

endmodule
