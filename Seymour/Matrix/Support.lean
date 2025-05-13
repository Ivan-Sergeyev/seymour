import Seymour.Basic.Fin


variable {X Y R : Type} [Zero R] [DecidableEq R]

@[simp]
def Matrix.support {X Y R : Type} [Zero R] [DecidableEq R] (A : Matrix X Y R) : Matrix X Y Z2 :=
  Matrix.of (if A · · = 0 then 0 else 1)

lemma Matrix.support_submatrix {X Y R : Type} [Zero R] [DecidableEq R] {X' Y' : Type}
    (A : Matrix X Y R) (f : X' → X) (g : Y' → Y) :
    A.support.submatrix f g = (A.submatrix f g).support :=
  rfl
