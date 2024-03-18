import CFLOBDD
import Construction

main : IO ()
main = do
  putStrLn "Dynamic tests besides static ones:"
  putStrLn $ "  Constructed CFLOBDD of (x₀ ⊕ x₁) ∨ (x₀ ∧ x₁ ∧ x₂) is correct: " ++ show xorOrAndCorrect
