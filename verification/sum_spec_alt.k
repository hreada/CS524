module SUM-SPEC
  imports ACTOR

  // Main claim
  rule
    <actors>
      <actor>
        <k> app(app(rec(lambda(sum, lambda(n, lambda(s,
                  if(eq?(n, 0), s, app(app(sum, minus(n, 1)), add(n, s))))))),
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
        <k> app(app(rec(lambda(sum, lambda(n, lambda(s,
                  if(eq?(n, 0), s, app(app(sum, minus(n, 1)), add(n, s))))))),
                minus(N:Int, 1)), add(N, S:Int))
            => N *Int (N +Int 1) /Int 2 +Int S
        </k>
        <id> initactor </id>
      </actor>
    </actors>
    requires N >Int 0

endmodule
