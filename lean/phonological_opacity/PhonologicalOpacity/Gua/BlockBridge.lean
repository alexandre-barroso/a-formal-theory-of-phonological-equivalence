import PhonologicalOpacity.Gua.Core
namespace Retained
def block (u : Input) (goal expected b : Nat) : Bool :=
  (List.range 169).all fun j => [0,1].all fun mode =>
    let i := 169*b+j
    if i == goal then score8 u mode i == expected else expected < score8 u mode i
theorem assemble_blocks {u : Input} {goal expected : Nat}
    (hf : u.focal.length = 3)
    (h : ∀ b < 13, block u goal expected b = true) : complete u goal expected = true := by
  apply List.all_eq_true.mpr
  intro i hi
  have hsize : 13^u.focal.length = 2197 := by rw [hf]; decide
  have hi' : i < 2197 := by simpa [carrier,hsize] using hi
  have hb : i / 169 < 13 := by omega
  have hj : i % 169 < 169 := Nat.mod_lt i (by decide)
  have hx := List.all_eq_true.mp (h (i/169) hb) (i%169) (List.mem_range.mpr hj)
  have he : 169*(i/169)+i%169 = i := by omega
  simpa only [he] using hx
#print axioms assemble_blocks
end Retained
