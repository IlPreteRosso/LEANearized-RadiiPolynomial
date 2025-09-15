default:
	lake clean
	lake build
	lake exe checkdecls blueprint/lean_decls
	leanblueprint web