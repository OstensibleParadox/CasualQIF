import CausalQIF.Graph.Examples

open Finset
open CausalQIF.Graph

example : computeMarkovBlanket chain3 1 = ({0, 2} : Finset (Fin 3)) := by decide
example : computeMarkovBlanket collider3 1 = ({0, 2} : Finset (Fin 3)) := by decide

example :
    generateMarkovBlanketConditions chain3 1
      = (({1} : Finset (Fin 3)), (∅ : Finset (Fin 3)), ({0, 2} : Finset (Fin 3))) := by
  decide

example :
    generateMarkovConditions chain3 1
      = (({1} : Finset (Fin 3)), (∅ : Finset (Fin 3)), ({0} : Finset (Fin 3))) := by
  decide
