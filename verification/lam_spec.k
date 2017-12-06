module LAM-SPEC
  imports ACTOR
  
  rule
    <actors>
      <actor>
        <k> app(lambda(Y:Id, Y), X:Int) => X ... </k>
        <id> initactor </id>
      </actor>
    </actors>

endmodule
