module SUM-SPEC
  imports ACTOR

  // Main claim
  rule
    <actors>
      <actor>
        <k> app(app(rec(lambda(#id("sum"), lambda(#id("n"), lambda(#id("s"),
                  if(eq?(#id("n"), 0), #id("s"), app(app(#id("sum"), minus(#id("n"), 1)), add(#id("n"), #id("s")))))))),
                N:Int), 0)
            => N *Int (N +Int 1) /Int 2
        </k>
        <id> initactor </id>
      </actor>
    </actors>
    requires N >=Int 0

  // Circularity
  rule
    <actors>
      <actor>
        <k> app(app(rec(lambda(#id("sum"), lambda(#id("n"), lambda(#id("s"),
                  if(eq?(#id("n"), 0), #id("s"), app(app(#id("sum"), minus(#id("n"), 1)), add(#id("n"), #id("s")))))))),
                minus(N:Int, 1)), add(N, S:Int))
            => N *Int (N +Int 1) /Int 2 +Int S
        </k>
        <id> initactor </id>
      </actor>
    </actors>
    requires N >Int 0

endmodule
