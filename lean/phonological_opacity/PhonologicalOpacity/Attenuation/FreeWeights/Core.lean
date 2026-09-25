import PhonologicalOpacity.Gua.Deletion.Core
namespace FreeWeights
open Retained Deletion
set_option maxRecDepth 100000
structure Polynomial where
  a : Int
  b : Int
  c : Int
  deriving DecidableEq, Repr
noncomputable def Polynomial.eval (p : Polynomial) (l : ℝ) : ℝ :=
  p.a + p.b*l + p.c*l^2
noncomputable def witness (l : ℝ) : Fin 9 → ℝ := ![3-4*l, 1, 1-2*l, 2-2*l, 2, 4, 4, 4, 4]
def polynomialOf (cf : List (Nat × Nat)) : Polynomial :=
  let o0 : Int := cf[0]!.1
  let n0 : Int := cf[0]!.2
  let o1 : Int := cf[1]!.1
  let n1 : Int := cf[1]!.2
  let o2 : Int := cf[2]!.1
  let n2 : Int := cf[2]!.2
  let o3 : Int := cf[3]!.1
  let n3 : Int := cf[3]!.2
  let o4 : Int := cf[4]!.1
  let n4 : Int := cf[4]!.2
  let o5 : Int := cf[5]!.1
  let n5 : Int := cf[5]!.2
  let o6 : Int := cf[6]!.1
  let n6 : Int := cf[6]!.2
  let o7 : Int := cf[7]!.1
  let n7 : Int := cf[7]!.2
  let o8 : Int := cf[8]!.1
  let n8 : Int := cf[8]!.2
  ⟨(3)*o0 + (1)*o1 + (1)*o2 + (2)*o3 + (2)*o4 + (4)*o5 + (4)*o6 + (4)*o7 + (4)*o8, (3)*n0 + (-4)*o0 + (1)*n1 + (1)*n2 + (-2)*o2 + (2)*n3 + (-2)*o3 + (2)*n4 + (4)*n5 + (4)*n6 + (4)*n7 + (4)*n8, (-4)*n0 + (-2)*n2 + (-2)*n3⟩

def polynomial (u : Input) (i : Nat) : Polynomial := polynomialOf (coefficients u 0 i)
noncomputable def pressure (u : Input) (w : Fin 9 → ℝ) (l : ℝ) (i : Nat) : ℝ :=
  realPressure u 0 w l i

theorem polynomial_expansion (cf : List (Nat × Nat)) (l : ℝ) :
    (polynomialOf cf).eval l =
    ∑ k : Fin 9, witness l k * ((cf[k.val]!.1 : ℝ) + l * (cf[k.val]!.2 : ℝ)) := by
  simp only [polynomialOf, Polynomial.eval, witness, Fin.sum_univ_succ]
  norm_num
  push_cast
  ring

theorem pressure_expansion (u : Input) (i : Nat) (l : ℝ) :
    pressure u (witness l) l i = (polynomial u i).eval l := by
  exact (polynomial_expansion (coefficients u 0 i) l).symm

theorem witness_nonnegative (l : ℝ) (h0 : 0 ≤ l) (h1 : l < 1/2) :
    ∀ k, 0 ≤ witness l k := by
  intro k
  fin_cases k <;> simp [witness] <;> linarith

def strictRow (p g : Polynomial) : Bool :=
  let a := p.a-g.a
  let b := p.b-g.b
  let c := p.c-g.c
  decide (0<a ∧ 0≤4*a+b ∧ 0≤4*a+2*b+c)

theorem strictRow_sound {p g : Polynomial} (h : strictRow p g = true)
    (l : ℝ) (h0 : 0 ≤ l) (h1 : l < 1/2) : g.eval l < p.eval l := by
  have hh : 0 < p.a-g.a ∧ 0 ≤ 4*(p.a-g.a)+(p.b-g.b) ∧
      0 ≤ 4*(p.a-g.a)+2*(p.b-g.b)+(p.c-g.c) := by simpa [strictRow] using h
  have ha : (0:ℝ) < p.a-g.a := by exact_mod_cast hh.1
  have hb : (0:ℝ) ≤ 4*(p.a-g.a)+(p.b-g.b) := by exact_mod_cast hh.2.1
  have hc : (0:ℝ) ≤ 4*(p.a-g.a)+2*(p.b-g.b)+(p.c-g.c) := by exact_mod_cast hh.2.2
  have ht : 0 < 1-2*l := by linarith
  have hA := mul_pos ha (sq_pos_of_pos ht)
  have hB := mul_nonneg (mul_nonneg hb h0) (le_of_lt ht)
  have hC := mul_nonneg hc (sq_nonneg l)
  dsimp [Polynomial.eval]
  nlinarith

def checkRow (u : Input) (g : Polynomial) (correct : List Nat) (i : Nat) : Bool :=
  if i ∈ correct then true else strictRow (polynomial u i) g

def checkBlock (u : Input) (g : Polynomial) (correct : List Nat) (b : Nat) : Bool :=
  (List.range 169).all fun j => checkRow u g correct (169*b+j)

def checkAll (u : Input) (g : Polynomial) (correct : List Nat) : Bool :=
  (carrier u).all (checkRow u g correct)

theorem assemble {u : Input} {g : Polynomial} {correct : List Nat} {n : Nat}
    (hn : 13^u.focal.length = 169*n)
    (h : ∀ b < n, checkBlock u g correct b = true) : checkAll u g correct = true := by
  apply List.all_eq_true.mpr
  intro i hi
  have hi' : i < 169*n := by simpa [carrier,hn] using hi
  have hb : i/169 < n := by omega
  have hj : i%169 < 169 := Nat.mod_lt i (by decide)
  have hx := List.all_eq_true.mp (h (i/169) hb) (i%169) (List.mem_range.mpr hj)
  have he : 169*(i/169)+i%169=i := by omega
  simpa only [he] using hx

theorem strict_separation {u : Input} {g : Polynomial} {correct : List Nat} {goal : Nat}
    (hc : checkAll u g correct = true) (hg : polynomial u goal = g)
    (l : ℝ) (h0 : 0 ≤ l) (h1 : l < 1/2)
    (i : Nat) (hi : i ∈ carrier u) (hw : i ∉ correct) :
    pressure u (witness l) l goal < pressure u (witness l) l i := by
  have hx := List.all_eq_true.mp hc i hi
  have hr : strictRow (polynomial u i) g = true := by simpa [checkRow, hw] using hx
  rw [pressure_expansion, pressure_expansion, hg]
  exact strictRow_sound hr l h0 h1
end FreeWeights
