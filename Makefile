# leanblueprint web updates blueprint/lean_decls
default:
	lake build
	leanblueprint web
	lake exe checkdecls blueprint/lean_decls

clean-build:
	lake clean
	lake exe cache get
	lake build
	leanblueprint web
	lake exe checkdecls blueprint/lean_decls

open:
	open blueprint/web/index.html

web:
	leanblueprint web
	lake exe checkdecls blueprint/lean_decls
clean:
	lake clean