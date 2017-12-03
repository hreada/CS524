module OMEGA-SPEC
  imports ACTOR
  
  rule
    <actors>
      <actor>
        <k> app(lambda(Y:Id, app(Y, Y)), lambda(Y, app(Y, Y))) => app(lambda(Y, app(Y, Y)), lambda(Y, app(Y, Y))) ... </k>
        <id> initactor </id>
      </actor>
    </actors>

endmodule
