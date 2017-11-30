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
  
  /* Atoms */
  
  syntax Atm  ::= Int
                | "t"
                | "nil"
  
  /* Values are terms that cannot rewrite anymore. */

  syntax Val  ::= Atm
                | Id                          // variables
                | "\\" Id "." Exp [binder]    // lambda abstraction
                | PairVal                     // pairs
  syntax PairVal ::= "pr" "(" Val "," Val ")"

  /* Expressions */
  
  syntax Exp  ::= Val                        // values
  
  syntax Exp  ::= "app" "(" Exp "," Exp ")" [seqstrict] // lambda application
  
  syntax Val  ::= "rec" "(" Exp ")" // call-by-value fixed-point combinator

  /* Expressions that are constructed using primitive operations. */
  
  syntax Exp  ::= "isatom"  "(" Exp                 ")"
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

  /* Expressions that are syntactic sugar.
   * They don't need the [strict] attribute as they simply rewrite
   * to expressions with primitive operations
   */
  syntax Exp  ::= "if" "(" Exp "," Exp "," Exp ")" 
                | "let" "{" Binding "}" Exp
                | "seq" "(" Exp "," Exp ")"
                | "letactor" "{" Bindings "}" Exp

  /* Bindings and lists of bindings */
  
  syntax Binding  ::= Id ":=" Exp
  syntax Bindings ::= List{Binding, ","}

  /* Meta-level information for rewriting */
  syntax KVariable ::= Id
  syntax KResult   ::= Val

  /* Expressions that are constructed using more operations. */
  syntax Exp ::= "mkset" "(" Exp ")"
               | "mkget" "(" Exp ")"
               | "set?"  "(" Exp ")"
               | "get?"  "(" Exp ")"
               | "eq?"   "(" Exp "," Exp ")" [strict]
               | "left"  "(" Exp ")"
               | "right" "(" Exp ")"
               | "cust"  "(" Exp ")"
  
  /* User-defined actor behavior as expressions. */
  syntax Exp ::= "treeprod"
               | "joincont"
               
  /* Message */
  syntax Message ::= "<" Val "<=" Val ">"
  
  /* Actor states */
  syntax AState  ::= "(" "?" Id ")"
                   | "(" Val ")"
                   | "[" Exp "]"    [strict]
                   
  /* Communication values */
  syntax CVal    ::= Atm
                   | Id
                   | "pr" "(" CVal "," CVal ")"

endmodule

module ACTOR

  imports ACTOR-SYNTAX
  
  syntax Id ::= "a"

  configuration <T color="red">
                  <actors color="orange">
                    <actor multiplicity="*" color="yellow">
                      <k color="green"> [ $PGM:Exp ] </k>
		      <id> a </id>
                    </actor>
                  </actors>
                  <messages> .List </messages>
                  <definedaddr> ListItem(a) </definedaddr>
                  <ext> .List </ext>
		  <recep> .List </recep>
                </T>
  
  /* Desugar rules for syntactic sugar (page 15) */
  
  rule if(E0:Exp, E1:Exp, E2:Exp)
    => app(br(E0, \!Z.E1, \!Z.E2), nil)
   
  rule let{X:Id := E0:Exp} E1
    => app(\X.E1, E0)
    
  rule seq(E0:Exp, E1:Exp)
    => app(app(\!Z.\!X.!X, E0), E1)
  
  rule letactor{.Bindings} E:Exp
    => E:Exp
  rule letactor{X1:Id := E1:Exp} E:Exp
    => let{X1 := newadr()}
         seq(initbeh(X1, E1), E)
  rule letactor{X1:Id := E1:Exp, X2:Id := E2:Exp} E:Exp // FIXME
    => let{X1 := newadr()} let{X2 := newadr()}
         seq(initbeh(X1, E1),
         seq(initbeh(X2, E2), E))
         
  /* Reduction rule for fixed-point combinator (I wrote it by myself) */
  
  rule rec(\B:Id . E:Exp) => E[rec(\B.E) / B] [structural]

  /* Reduction rules of expressions (page 18) */
  
  /* (beta-v) */
  rule app(\X:Id . E:Exp, V:Val) 
    => E[V / X]
  
  /* (delta) rules are defined for each operators */
  
  /* (br) */
  rule br(nil  , V1:Val, V2:Val) => V2
  rule br(V:Val, V1:Val, V2:Val) => V1       // FIXME consider known addresses
    requires V:Val =/=K nil
    
  /* (ispr) */
  rule ispr(V:PairVal) => t
  rule ispr(V:Val)     => nil                // FIXME consider known addresses
    requires notBool(isPairVal(V))
  
  /* (fst) & (snd) */
  rule fst(pr(V1:Val, V2:Val)) => V1:Val
  rule snd(pr(V1:Val, V2:Val)) => V2:Val
  
  /* (eq) */
  rule eq?(V1:Atm, V2:Atm) => t   requires V1 ==K  V2
  rule eq?(V1:Atm, V2:Atm) => nil requires V1 =/=K V2
  
  
  
  /* Transition rules for configurations (page 19) */
  
  /* <init : a, a'> */
  rule <k> initbeh(A', V:Val) => nil </k>

  /*     <actor>
         <k> ( ? A ) => ( V ) </k>
         <id> A' </id>
       </actor> */


       
  
  /* <new : a, a'> */
  rule <actor>
         <k> newadr() => !A':Id ... </k>
         <id> A </id>
       </actor>
       (.Bag => <actor>
                  <k> ( ? A ) </k>
                  <id> !A' </id>
                </actor>)
       <definedaddr> Ads => Ads ListItem(!A') </definedaddr>

  
endmodule

































