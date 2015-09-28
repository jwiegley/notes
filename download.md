These options make different choices as to what elements are installed
*globally* across your whole system and which ones are maintained in
project-specific environments. Global installations allow more sharing across
users and across projects, but at the cost of potentially inflexible coupling
of dependencies between separate projects. Therefore, sandboxes are usually
suggested to avoid this coupling. Global installation is the standard
operating mode of the Haskell Platform, while sandboxes are default mode for
Stack.
