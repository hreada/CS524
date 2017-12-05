module SUM-SPEC
  imports ACTOR
  
  // rule
  //   <actors>
  //     <actor>
  //       <k> app(app(rec(lambda(#id("sum"), lambda(#id("n"), lambda(#id("s"),
  //                 if(eq?(#id("n"), 0), #id("s"), app(app(#id("sum"), minus(#id("n"), 1)), add(#id("n"), #id("s")))))))),
  //               N:Int), 0)
  //           => N *Int (N +Int 1) /Int 2
  //       </k>
  //       <id> initactor </id>
  //     </actor>
  //   </actors>
  //   requires N >=Int 0

  rule
    <actors>
      <actor>
        <k> if(eq?(#id("n"), 0):Exp, #id("s"), app(app(#id("sum"), minus(#id("n"), 1):Exp):Exp, add(#id("n"), #id("s")):Exp):Exp):Exp
            => N *Int (N +Int 1) /Int 2 +Int S
        </k>
        <env> #id("s") |-> S:Int
              #id("sum") |-> closure($x |-> closure(.Map, $x, app(lambda(#id("sum"), lambda(#id("n"), lambda(#id("s"), if(eq?(#id("n"), 0):Exp, #id("s"), app(app(#id("sum"), minus(#id("n"), 1):Exp):Exp, add(#id("n"), #id("s")):Exp):Exp):Exp):Exp):Exp):Exp, lambda($y, app(app($x, $x):Exp, $y):Exp):Exp):Exp), $y, app(app($x, $x):Exp, $y):Exp)
              #id("n") |-> N:Int
              $x |-> closure(.Map, $x, app(lambda(#id("sum"), lambda(#id("n"), lambda(#id("s"), if(eq?(#id("n"), 0):Exp, #id("s"), app(app(#id("sum"), minus(#id("n"), 1):Exp):Exp, add(#id("n"), #id("s")):Exp):Exp):Exp):Exp):Exp):Exp, lambda($y, app(app($x, $x):Exp, $y):Exp):Exp):Exp)
        </env>
        <id> initactor </id>
      </actor>
    </actors>
    <definedaddr> ListItem(initactor) </definedaddr>
    requires N >=Int 0

endmodule
