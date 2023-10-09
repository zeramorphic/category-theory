import Lake
open Lake DSL

package «category-theory» {
  -- add any package configuration options here
}

require aesop from git "https://github.com/JLimperg/aesop"

@[default_target]
lean_lib CategoryTheory {
  -- add any library configuration options here
}
