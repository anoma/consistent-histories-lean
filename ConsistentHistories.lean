import ConsistentHistories.Basic
import ConsistentHistories.Foundation
import ConsistentHistories.Models
import ConsistentHistories.Routes
import ConsistentHistories.AlternativePresentation
import ConsistentHistories.PaperTargets.Conclusions

/-!
Root module for the ConsistentHistories formalization.

The library is organized by role: reusable foundations (`ConsistentHistories.Foundation`),
paper-facing targets (`ConsistentHistories.PaperTargets`), concrete models
(`ConsistentHistories.Models`), the alternative presentation
(`ConsistentHistories.AlternativePresentation`), and downstream routes (`ConsistentHistories.Routes`)
are kept under explicit roots. `FORMALIZATION_MAP.md` links each numbered paper
item to its Lean declaration(s).
-/
