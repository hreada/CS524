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

  syntax Atom ::= Int   /* FIXME:: should be non-negative integers */
                | Bool
                | "t"
		| "nil"

  /* Values are expressions that cannot rewrite anymore */
  syntax Val  ::= Atom
                | Id
                | "\\" Id "." Exp [binder]
	        | "pr" "(" Val "," Val ")"

  /* Lambda-calculus application */
  syntax Exp  ::= "app"     "(" Exp "," Exp         ")" [strict]

  /* Lambda-calculus application: prefix form.
   * This is useful in defining actors' behavior
   */
  syntax Exp  ::= Id "(" Exp ")"                        [strict]

  /* Primitive operations */
  syntax Exp  ::= Val
                | "rec"     "(" Exp                 ")"
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
                | Exp "*" Exp                             [strict]

  /* Non-primitive operations */
  syntax Exp  ::= "if" "(" Exp "," Exp "," Exp ")" [strict(1)]
                | "let" "{" BindingExp "}" Exp
                | "seq" "(" Exp "," Exp ")"
                | "letactor" "{" BindingExps "}" Exp

  /* Binding expressions */
  syntax BindingExp  ::= Id ":=" Exp
  syntax BindingExps ::= List{BindingExp, ","}

  /* Expressions */
  syntax Exps  ::= List{Exp, ","}

  /* Meta-level */
  syntax KVariable ::= Id
  syntax KResult   ::= Val

  /* User-defined Part */
  syntax Exp ::= "mkset" "(" Exp ")"
               | "mkget" "(" Exp ")"
               | "set?"  "(" Exp ")"
               | "get?"  "(" Exp ")"
               | "eq?"   "(" Exp "," Exp ")" [strict]
               | "left"  "(" Exp ")"
               | "right" "(" Exp ")"
               | "isnat" "(" Exp ")"
  
  /* User-defined actor behavior */
  syntax Exp ::= "treeprod"
               | "joincont"


  /* Actor Id */
  syntax ActorId ::= Int 
  syntax ActorIds ::= List{Int, ","}

  /* Messages */
  syntax Message ::= Int /* FIXME */
  syntax Messages ::= List{Message, ","}

endmodule

module ACTOR

  imports ACTOR-SYNTAX

  /* TODO:: Add a <actor-id> or <actor-name> cell inside the <actor> cell
   *        Add <receptionist> and <external> cells in <T>
   *        Add <messages> cell in <T>
   */
  /* We might want to separate some of the things such as messages to
   * another K module, but let's do it here and consider separating them
   * later.
   */
  configuration <T>
                  <actors>
                    <actor multiplicity="*">
                      <k> $PGM:Exp </k>
		      <id> 0 </id> /* FIXME:: initialize to different values */
                    </actor>
                  </actors>
		  <recep>
		    .ActorIds
		  </recep>
		  <ext>
		    .ActorIds
		  </ext>
		  <messages>
		    .Messages
		  </messages>
                </T>

  rule app(\ X:Id . E:Exp, V:Val) => E[V / X]
  rule B:Id(E:Exp) => app(B, E)

  rule if (true,  E, _) => E
  rule if (false, _, E) => E

  rule eq?(V1:Val, V2:Val) => V1 ==K V2

  /* rule for recursion: rec(\b.E) = E[rec(\b.E)/b] */
  rule rec(\ B:Id . E:Exp) => E[rec(\B.E) / B]
  
  syntax Id ::= "b"
              | "self"
              | "m"
              | "cust"
              | "nargs"
              | "firstnum"
              | "num"
              | "newcust"
  
  /* User-defined Part */
  rule treeprod =>
    rec(\b.\self.\m.
      seq(become(b(self),
        if(isnat(tree(m)),
           send(cust(m), tree(m)),
           letactor{newcust := joincont(cust(m),0,nil)}
             seq(send(self, pr(left(tree(m)), newcust)),
                 send(self, pr(right(tree(m)), newcust)))))))
  rule joincont =>
    rec(\b.\cust.\nargs.\firstnum.\num.
      if(eq(nargs,0),
         become(b(cust,1,num)),
         seq(become(sink),
             send(cust,firstnum * num))))

endmodule
