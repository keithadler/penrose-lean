import Lean
open Lean Widget

/-!
# The right graphs: Penrose diagrams

> The worst part about the "linear algebra is graph theory" larp is that it's kinda true but you're
> using the wrong graphs. They're called Penrose diagrams. (doomslide)

In a Penrose diagram a box is a matrix, a wire is an index, and joining two wires means summing over
the index they share. A bent wire is the identity matrix read sideways (a cup or a cap), and a diagram
with no loose ends is a number.

This file makes that a definition, not a picture: `D a b` is the syntax of diagrams with `a` wires
coming in at the top and `b` going out at the bottom, and `eval n` gives each one its meaning when every
wire carries an index below `n`. The theorems then show the rules people draw are true for every
dimension `n` and every matrix:

* two boxes joined by a wire are the matrix product (`seq_box`);
* a zig-zag pulls straight into a plain wire (`snake`, `snake'`);
* a box turned upside down by bending its wires is the transpose (`bend_transpose`);
* closing a box's wire into a loop is the trace (`loop_trace`), and a bare loop is the dimension
  (`loop_dim`);
* a box slides around a bend, turning into its transpose (`slide`), so boxes slide round a loop and
  `tr (A B) = tr (B A)` (`trace_cyclic`);
* boxes side by side are the Kronecker product (`par_box`), and they pass through a crossing
  (`cross_natural`);
* a row of `k` copies of `A` is `Aᵏ`, and closing it gives `tr (Aᵏ)`, the total weight of the closed
  `k`-step walks in the other kind of graph (`chain_pow`, `ring_trace_pow`).

Core Lean only, no Mathlib. Put the cursor on `#widget` at the bottom and open the Infoview tab to see
the diagrams drawn for the matrix from the post.
-/

namespace Penrose

/-! ## Sums and the Kronecker delta -/

/-- `sumTo n f` is `f 0 + … + f (n - 1)`. -/
def sumTo : Nat → (Nat → Rat) → Rat
  | 0, _ => 0
  | n + 1, f => sumTo n f + f n

/-- The Kronecker delta: 1 when the indices agree. It is what a plain wire means. -/
def δ (i j : Nat) : Rat := if i = j then 1 else 0

/-- The sum over every list of `k` indices below `n`: what joining `k` wires means. -/
def sumTup (n : Nat) : Nat → (List Nat → Rat) → Rat
  | 0, f => f []
  | k + 1, f => sumTo n (fun i => sumTup n k (fun t => f (i :: t)))

theorem δ_comm (i j : Nat) : δ i j = δ j i := by
  unfold δ; by_cases h : i = j <;> simp [h, eq_comm]

theorem δ_self (i : Nat) : δ i i = 1 := by simp [δ]

theorem sumTo_congr {n : Nat} {f g : Nat → Rat} (h : ∀ i, i < n → f i = g i) : sumTo n f = sumTo n g := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [sumTo]; rw [ih (fun i hi => h i (by omega)), h n (by omega)]

attribute [local simp] Rat.add_zero Rat.zero_add Rat.mul_zero Rat.zero_mul Rat.mul_one Rat.one_mul

theorem sumTo_add (n : Nat) (f g : Nat → Rat) :
    sumTo n (fun i => f i + g i) = sumTo n f + sumTo n g := by
  induction n with
  | zero => simp [sumTo]
  | succ n ih => simp only [sumTo, ih]; grind

theorem sumTo_mul_left (n : Nat) (c : Rat) (f : Nat → Rat) :
    sumTo n (fun i => c * f i) = c * sumTo n f := by
  induction n with
  | zero => simp [sumTo]
  | succ n ih => simp only [sumTo, ih]; grind

theorem sumTo_mul_right (n : Nat) (c : Rat) (f : Nat → Rat) :
    sumTo n (fun i => f i * c) = sumTo n f * c := by
  induction n with
  | zero => simp [sumTo]
  | succ n ih => simp only [sumTo, ih]; grind

theorem sumTo_const_zero (n : Nat) : sumTo n (fun _ => 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [sumTo, ih]

theorem sumTo_one (n : Nat) : sumTo n (fun _ => 1) = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [sumTo, ih]; push_cast; rfl

/-- Summing a delta picks out one term: a wire joined to a wire is one wire. -/
theorem sumTo_delta {n i : Nat} (hi : i < n) (f : Nat → Rat) : sumTo n (fun j => δ i j * f j) = f i := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [sumTo]
    by_cases h : i < n
    · rw [ih h]; simp [δ, show i ≠ n by omega]
    · have hi : i = n := by omega
      subst hi
      rw [sumTo_congr (g := fun _ => 0) (fun j hj => by simp [δ, show i ≠ j by omega]), sumTo_const_zero]
      simp [δ]

theorem sumTo_delta' {n i : Nat} (hi : i < n) (f : Nat → Rat) : sumTo n (fun j => δ j i * f j) = f i := by
  rw [sumTo_congr (g := fun j => δ i j * f j) (fun j _ => by rw [δ_comm])]; exact sumTo_delta hi f

/-! ### Collapsing sums

These let `simp` do the bookkeeping of Penrose's convention: a delta becomes an `if`, an `if` that does
not mention the summed index moves outside the sum, and a sum over an index pinned by an equation
collapses to one term. -/

theorem ite_mul_zero (p : Prop) [Decidable p] (a b : Rat) :
    (if p then a else 0) * b = if p then a * b else 0 := by split <;> simp

theorem mul_ite_zero (p : Prop) [Decidable p] (a b : Rat) :
    a * (if p then b else 0) = if p then a * b else 0 := by split <;> simp

theorem sumTo_ite_const (n : Nat) (p : Prop) [Decidable p] (f : Nat → Rat) :
    sumTo n (fun j => if p then f j else 0) = if p then sumTo n f else 0 := by
  split
  · rfl
  · exact sumTo_const_zero n

theorem sumTo_ite_eq (n i : Nat) (f : Nat → Rat) :
    sumTo n (fun j => if i = j then f j else 0) = if i < n then f i else 0 := by
  split
  · rename_i hi
    have := sumTo_delta hi f
    rw [← this]; apply sumTo_congr; intro j _; simp [δ]; split <;> simp
  · rename_i hi
    rw [sumTo_congr (g := fun _ => 0) (fun j hj => by simp [show i ≠ j by omega]), sumTo_const_zero]

theorem sumTo_ite_eq' (n i : Nat) (f : Nat → Rat) :
    sumTo n (fun j => if j = i then f j else 0) = if i < n then f i else 0 := by
  rw [← sumTo_ite_eq]; apply sumTo_congr; intro j _; simp [eq_comm]

theorem sumTo_ite_lt (n : Nat) (f g : Nat → Rat) :
    sumTo n (fun j => if j < n then f j else g j) = sumTo n f := by
  apply sumTo_congr; intro j hj; simp [hj]

theorem δ_eq (i j : Nat) : δ i j = if i = j then 1 else 0 := rfl

/-- Sums can be taken in either order. -/
theorem sumTo_comm (n m : Nat) (f : Nat → Nat → Rat) :
    sumTo n (fun i => sumTo m (fun j => f i j)) = sumTo m (fun j => sumTo n (fun i => f i j)) := by
  induction n with
  | zero => simp [sumTo, sumTo_const_zero]
  | succ n ih => simp only [sumTo, ih]; rw [← sumTo_add]

theorem sumTup_mul_left (n : Nat) (c : Rat) : ∀ (k : Nat) (f : List Nat → Rat),
    sumTup n k (fun t => c * f t) = c * sumTup n k f := by
  intro k; induction k with
  | zero => intro f; rfl
  | succ k ih => intro f; simp only [sumTup]; rw [← sumTo_mul_left]; exact sumTo_congr (fun i _ => ih _)

theorem sumTup_mul_right (n : Nat) (c : Rat) : ∀ (k : Nat) (f : List Nat → Rat),
    sumTup n k (fun t => f t * c) = sumTup n k f * c := by
  intro k; induction k with
  | zero => intro f; rfl
  | succ k ih => intro f; simp only [sumTup]; rw [← sumTo_mul_right]; exact sumTo_congr (fun i _ => ih _)

theorem sumTo_sumTup (n m : Nat) : ∀ (k : Nat) (f : Nat → List Nat → Rat),
    sumTo m (fun i => sumTup n k (fun t => f i t)) = sumTup n k (fun t => sumTo m (fun i => f i t)) := by
  intro k; induction k with
  | zero => intro f; rfl
  | succ k ih => intro f; simp only [sumTup]; rw [sumTo_comm]; exact sumTo_congr (fun j _ => ih _)

/-- Sums over two sets of joined wires can be taken in either order. -/
theorem sumTup_comm (n : Nat) : ∀ (k l : Nat) (f : List Nat → List Nat → Rat),
    sumTup n k (fun s => sumTup n l (fun t => f s t)) = sumTup n l (fun t => sumTup n k (fun s => f s t)) := by
  intro k; induction k with
  | zero => intro l f; rfl
  | succ k ih =>
    intro l f; simp only [sumTup]
    rw [sumTo_congr (fun i _ => ih l (fun s t => f (i :: s) t))]
    exact sumTo_sumTup n n l (fun i t => sumTup n k (fun s => f (i :: s) t))

/-! ## Diagrams -/

/-- A Penrose diagram with `a` wires coming in at the top and `b` going out at the bottom. -/
inductive D : Nat → Nat → Type
  /-- A box: the matrix `M`, its row index on the wire in, its column index on the wire out. -/
  | box (M : Nat → Nat → Rat) : D 1 1
  /-- A plain wire. -/
  | wire : D 1 1
  /-- A wire bent into a cup: two wires out, none in. -/
  | cup : D 0 2
  /-- A wire bent into a cap: two wires in, none out. -/
  | cap : D 2 0
  /-- Two wires crossing. -/
  | cross : D 2 2
  /-- One diagram above another, the outputs of the first joined to the inputs of the second. -/
  | seq {a b c : Nat} : D a b → D b c → D a c
  /-- Two diagrams side by side. -/
  | par {a b c d : Nat} : D a b → D c d → D (a + c) (b + d)

@[inherit_doc] scoped infixr:60 " ≫ " => D.seq
@[inherit_doc] scoped infixl:70 " ⊗ " => D.par

/-- What a diagram means when every wire carries an index below `n`: the number it gives for each
choice of indices on its loose ends, the ones coming in `x` and the ones going out `y`. Joined wires are
summed over, which is the whole of Penrose's convention. -/
def eval (n : Nat) : {a b : Nat} → D a b → List Nat → List Nat → Rat
  | _, _, .box M, x, y => M (x.getD 0 0) (y.getD 0 0)
  | _, _, .wire, x, y => δ (x.getD 0 0) (y.getD 0 0)
  | _, _, .cup, _, y => δ (y.getD 0 0) (y.getD 1 0)
  | _, _, .cap, x, _ => δ (x.getD 0 0) (x.getD 1 0)
  | _, _, .cross, x, y => δ (x.getD 0 0) (y.getD 1 0) * δ (x.getD 1 0) (y.getD 0 0)
  | _, _, @D.seq _ b _ S T, x, z => sumTup n b (fun y => eval n S x y * eval n T y z)
  | _, _, @D.par a b _ _ S T, x, z => eval n S (x.take a) (z.take b) * eval n T (x.drop a) (z.drop b)

open D

/-- Evaluates a diagram and collapses its sums: unfold `eval`, turn each wire into an `if`, move every
`if` that does not mention a summed index out of its sum, collapse each sum over a pinned index, and
settle the index equations that are left. -/
macro "penrose" : tactic => `(tactic| (
  simp only [eval, sumTup, List.getD_cons_zero, List.getD_cons_succ, List.take_succ_cons,
    List.take_zero, List.drop_succ_cons, List.drop_zero, List.take_nil]
  simp (config := { contextual := true }) only [δ_eq, ite_mul_zero, mul_ite_zero, sumTo_ite_const,
    sumTo_ite_eq, sumTo_ite_eq', sumTo_ite_lt, sumTo_one, Rat.mul_one, Rat.one_mul, Rat.mul_zero, Rat.zero_mul,
    ite_self, ite_true, ite_false, sumTo_const_zero, *]
  try (repeat' split) <;> first | rfl | (exfalso; omega) | simp_all | skip))

/-! ## The rules, for every dimension and every matrix -/

/-- Two boxes joined by a wire are the matrix product. -/
theorem seq_box (n : Nat) (A B : Nat → Nat → Rat) (i k : Nat) :
    eval n (box A ≫ box B) [i] [k] = sumTo n (fun j => A i j * B j k) := by
  simp [eval, sumTup]

/-- The zig-zag: a cup on the left, then a cap on the right. -/
def zigzag : D 1 1 := (cup ⊗ wire : D 1 3) ≫ (wire ⊗ cap : D 3 1)

/-- The zig-zag pulls straight: a cup then a cap is a plain wire. -/
theorem snake (n : Nat) (i k : Nat) (hi : i < n) : eval n zigzag [i] [k] = eval n wire [i] [k] := by
  unfold zigzag; penrose

/-- The other zig-zag: a cup on the right, then a cap on the left. -/
def zigzag' : D 1 1 := (wire ⊗ cup : D 1 3) ≫ (cap ⊗ wire : D 3 1)

theorem snake' (n : Nat) (i k : Nat) (hi : i < n) : eval n zigzag' [i] [k] = eval n wire [i] [k] := by
  unfold zigzag'; penrose

/-- A box turned upside down: its wires bent round with a cup below and a cap above. -/
def bend (S : D 1 1) : D 1 1 := (cup ⊗ wire : D 1 3) ≫ (wire ⊗ S ⊗ wire : D 3 3) ≫ (wire ⊗ cap : D 3 1)

/-- The transpose of a matrix. -/
def transpose (A : Nat → Nat → Rat) : Nat → Nat → Rat := fun i j => A j i

/-- Bending a box's wires round turns it into its transpose. -/
theorem bend_transpose (n : Nat) (A : Nat → Nat → Rat) (i k : Nat) (hi : i < n) (hk : k < n) :
    eval n (bend (box A)) [i] [k] = eval n (box (transpose A)) [i] [k] := by
  unfold bend transpose; penrose

/-- A diagram with its output wire bent round and joined to its input: no loose ends left. -/
def loop (S : D 1 1) : D 0 0 := cup ≫ (S ⊗ wire : D 2 2) ≫ cap

/-- The trace of a matrix. -/
def trace (n : Nat) (A : Nat → Nat → Rat) : Rat := sumTo n (fun i => A i i)

/-- Closing any diagram into a loop sums its diagonal. -/
theorem loop_eval (n : Nat) (S : D 1 1) : eval n (loop S) [] [] = sumTo n (fun i => eval n S [i] [i]) := by
  unfold loop; penrose

/-- A box closed into a loop is the trace. -/
theorem loop_trace (n : Nat) (A : Nat → Nat → Rat) : eval n (loop (box A)) [] [] = trace n A := by
  rw [loop_eval]; rfl

/-- A bare loop is the dimension. -/
theorem loop_dim (n : Nat) : eval n (loop wire) [] [] = n := by
  rw [loop_eval]; simp [eval, δ_self, sumTo_one]

/-- Boxes slide round a loop: `tr (A B) = tr (B A)`. -/
theorem trace_cyclic (n : Nat) (A B : Nat → Nat → Rat) :
    eval n (loop (box A ≫ box B)) [] [] = eval n (loop (box B ≫ box A)) [] [] := by
  rw [loop_eval, loop_eval]
  simp only [eval, sumTup, List.getD_cons_zero]
  rw [sumTo_comm]
  apply sumTo_congr; intro i _; apply sumTo_congr; intro j _
  exact Rat.mul_comm _ _

/-- A box slides along a bend, turning into its transpose. -/
theorem slide (n : Nat) (A : Nat → Nat → Rat) (j k : Nat) (hj : j < n) (hk : k < n) :
    eval n (cup ≫ (box A ⊗ wire : D 2 2)) [] [j, k] = eval n (cup ≫ (wire ⊗ box (transpose A) : D 2 2)) [] [j, k] := by
  unfold transpose; penrose

/-- Boxes side by side are the Kronecker product. -/
theorem par_box (n : Nat) (A B : Nat → Nat → Rat) (i j k l : Nat) :
    eval n (box A ⊗ box B) [i, j] [k, l] = A i k * B j l := by
  simp [eval]

/-- Boxes pass through a crossing, swapping sides. -/
theorem cross_natural (n : Nat) (A B : Nat → Nat → Rat) (i j k l : Nat) (hi : i < n) (hj : j < n)
    (hk : k < n) (hl : l < n) :
    eval n ((box A ⊗ box B : D 2 2) ≫ cross) [i, j] [k, l] = eval n (cross ≫ (box B ⊗ box A : D 2 2)) [i, j] [k, l] := by
  penrose; grind

/-- Two crossings undo each other. -/
theorem cross_cross (n : Nat) (i j k l : Nat) (hi : i < n) (hj : j < n) :
    eval n (cross ≫ cross) [i, j] [k, l] = eval n (wire ⊗ wire : D 2 2) [i, j] [k, l] := by
  penrose

/-- The `k`-th power of a matrix. -/
def pow (n : Nat) (A : Nat → Nat → Rat) : Nat → Nat → Nat → Rat
  | 0 => fun i j => δ i j
  | k + 1 => fun i j => sumTo n (fun m => A i m * pow n A k m j)

/-- A row of `k` copies of a box. -/
def chain (A : Nat → Nat → Rat) : Nat → D 1 1
  | 0 => wire
  | k + 1 => box A ≫ chain A k

/-- A row of `k` boxes is the `k`-th power. -/
theorem chain_pow (n : Nat) (A : Nat → Nat → Rat) (k i j : Nat) :
    eval n (chain A k) [i] [j] = pow n A k i j := by
  induction k generalizing i j with
  | zero => simp [chain, pow, eval]
  | succ k ih =>
    simp only [chain, pow, eval, sumTup, List.getD_cons_zero]
    apply sumTo_congr; intro m _; rw [ih]

/-- Closing a row of `k` boxes into a ring gives `tr (Aᵏ)`, the total weight of the closed `k`-step
walks in the matrix's graph. -/
theorem ring_trace_pow (n : Nat) (A : Nat → Nat → Rat) (k : Nat) :
    eval n (loop (chain A k)) [] [] = trace n (pow n A k) := by
  rw [loop_eval]; apply sumTo_congr; intro i _; rw [chain_pow]

/-! ## Why the pictures are unambiguous -/

/-- Stacking is associative: a tall diagram means the same however its layers are grouped. -/
theorem seq_assoc (n : Nat) {a b c d : Nat} (S : D a b) (T : D b c) (U : D c d) (x z : List Nat) :
    eval n ((S ≫ T) ≫ U) x z = eval n (S ≫ (T ≫ U)) x z := by
  simp only [eval]
  have h1 : ∀ w, (sumTup n b fun y => eval n S x y * eval n T y w) * eval n U w z =
      sumTup n b (fun y => eval n S x y * eval n T y w * eval n U w z) :=
    fun w => (sumTup_mul_right n _ b _).symm
  have h2 : ∀ y, eval n S x y * (sumTup n c fun w => eval n T y w * eval n U w z) =
      sumTup n c (fun w => eval n S x y * (eval n T y w * eval n U w z)) :=
    fun y => (sumTup_mul_left n _ c _).symm
  simp only [h1, h2]
  rw [sumTup_comm n c b]
  congr; funext y; congr; funext w; exact Rat.mul_assoc _ _ _

/-- A plain wire above a box changes nothing. -/
theorem wire_seq (n : Nat) (S : D 1 1) (i k : Nat) (hi : i < n) : eval n (wire ≫ S) [i] [k] = eval n S [i] [k] := by
  simp only [eval, sumTup, List.getD_cons_zero]
  have := sumTo_delta hi (fun j => eval n S [j] [k])
  simpa using this

/-- A plain wire below a box changes nothing. -/
theorem seq_wire (n : Nat) (S : D 1 1) (i k : Nat) (hk : k < n) : eval n (S ≫ wire) [i] [k] = eval n S [i] [k] := by
  simp only [eval, sumTup, List.getD_cons_zero]
  rw [sumTo_congr (g := fun j => δ k j * eval n S [i] [j]) (fun j _ => by rw [δ_comm]; grind)]
  exact sumTo_delta hk _

/-! ## The matrix from the post -/

/-- The matrix in the "graph theory and linear algebra" post. -/
def M : Nat → Nat → Rat := fun i j =>
  ([[1/2, 1, 0], [1/5, 0, 11/5], [9/5, 2, 0]].getD i []).getD j 0

/-- Its trace, read off the loop diagram by Lean's kernel. -/
theorem post_trace : eval 3 (loop (box M)) [] [] = 1/2 := by decide +kernel

/-- A bare loop in three dimensions. -/
theorem post_loop : eval 3 (loop wire) [] [] = 3 := by decide +kernel

/-- Bent round, the box's corner entry `1.8` moves across the diagonal. -/
theorem post_bend : eval 3 (bend (box M)) [0] [2] = 9/5 ∧ eval 3 (bend (box M)) [2] [0] = 0 := by
  decide +kernel

/-- A ring of two boxes: `tr (M²) = 9.45`, the total weight of the closed two-step walks. -/
theorem post_ring : eval 3 (loop (chain M 2)) [] [] = 189/20 := by decide +kernel

/-! ## The widget -/

private def ratJson (r : Rat) : Json := Json.arr #[toJson r.num, toJson r.den]

private def matJson (f : Nat → Nat → Rat) : Json :=
  Json.arr ((List.range 3).map fun i => Json.arr ((List.range 3).map fun j => ratJson (f i j)).toArray).toArray

/-- Everything the widget shows, computed here by `eval` on the diagrams themselves. -/
def widgetProps : Json :=
  let e11 := fun (S : D 1 1) => matJson (fun i j => eval 3 S [i] [j])
  Json.mkObj [
    ("M", matJson M),
    ("box", e11 (box M)),
    ("square", e11 (box M ≫ box M)),
    ("zigzag", e11 zigzag),
    ("bend", e11 (bend (box M))),
    ("trace", ratJson (eval 3 (loop (box M)) [] [])),
    ("dim", ratJson (eval 3 (loop wire) [] [])),
    ("slideAB", ratJson (eval 3 (loop (box M ≫ box (transpose M))) [] [])),
    ("slideBA", ratJson (eval 3 (loop (box (transpose M) ≫ box M)) [] [])),
    ("rings", Json.arr ((List.range 7).map fun k => ratJson (eval 3 (loop (chain M k)) [] [])).toArray)]

@[widget_module]
def PenroseWidget : Widget.Module where
  javascript := include_str "widget" / "Penrose.js"

end Penrose

open Penrose in
#widget PenroseWidget with widgetProps
