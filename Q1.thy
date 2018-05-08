  theory Q1
    imports
begin 
theorem AB_PROVA_BA: "(A^B) ⟶ (B^A)"
proof ―
  have ab:"(A^B) ⟹ (B^A) "
  proof ―
    assume ab: "A^B"
    from ab have a: "A" by (rule conjE)
    from ab have b: "B" by (rule conjE)
    from b and a have ba: "B^A" by (rule conjI)
  qed
  from ab show "(A^B)⟶(B^A)" by (rule impI)
qed
end
