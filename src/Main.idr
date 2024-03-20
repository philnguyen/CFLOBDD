import CFLOBDD
import Construction1
import Tests

main : IO ()
main = do
  putStrLn "Dynamic tests besides static ones:"
  putStrLn $ "  Constructed CFLOBDD of (x₀ ⊕ x₁) ∨ (x₀ ∧ x₁ ∧ x₂) is correct: " ++ show xorOrAndCorrect
