 theory Q2
imports Main
begin

theorem ex1 : 
  assumes rpq: "R⟶P∨Q"
 and rfalseq: "R⟶¬Q"
    shows "R⟶P"
proof -
   have rp: "R⟹P"
   proof -
     assume r: "R"
     from rpq and r have  pq: "P∨Q" by (rule impE) 
     from rfalseq and r have nq: "¬Q" by (rule impE)

     have npfalse: "¬P ⟹ False"
     proof -
       assume np: "¬P"
       
       have falseq: "Q ⟹ False"
       proof -
         assume q: "Q"
         from nq and q show "False" by (rule notE)
       qed
      
       have pfalse: "P ⟹ False"
       proof - 
         assume p: "P"
         from np and p show "False" by (rule notE)
       qed
       
       from pq and pfalse and falseq show "False" by (rule disjE)
     qed
     from npfalse have nnp: "¬¬P" by (rule notI)
     from nnp show p: "P" by (rule notnotD)
   qed
   from rp show "R ⟶ P" by (rule impI)
 qed
end
