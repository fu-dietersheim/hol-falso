theory Fermat
imports Main HOLF
begin

text {*
  The Fermat-Wiles theorem: If @{term "n>2"}, no 
  @{term "n"}-th power of a positive integer can be the 
  sum of the @{term "n"}-th powers of two positive integers.
  
  Note how the length and complexity of this proof compares 
  to Wiles' original proof.
  
  "Cuius rei demonstrationem mirabilem sane deteximus
   Quodque marginis exiguitas caperet."
*}
lemma fermat:
  fixes n :: nat and a :: nat
  assumes "n > 2" "a > 0" "b > 0" "c > 0"
  shows "a^n + b^n \<noteq> c^n"
using assms
apply exfalso
done

end
