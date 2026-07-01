import ContForm.Basic
import ContForm.Foundation
import ContForm.Models
import ContForm.Routes
import ContForm.AlternativePresentation
import ContForm.PaperTargets.Conclusions

/-!
Root module for the ContForm formalization.

The library is organized by role: reusable foundations (`ContForm.Foundation`),
paper-facing targets (`ContForm.PaperTargets`), concrete models
(`ContForm.Models`), the alternative presentation
(`ContForm.AlternativePresentation`), and downstream routes (`ContForm.Routes`)
are kept under explicit roots. `FORMALIZATION_MAP.md` links each numbered paper
item to its Lean declaration(s).
-/
