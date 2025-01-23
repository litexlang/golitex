package parser

func (t *DefConceptStmt) toTopStmt() TopStmt {
	return &DefConceptTopStmt{true, *t}
}

func (t *DefPropertyStmt) toTopStmt() TopStmt {
	return &DefPropertyTopStmt{true, *t}
}

func (t *IfStmt) toTopStmt() TopStmt {
	return &IfFactTopStmt{true, *t}
}

func (t *PtyStmt) toTopStmt() TopStmt {
	return &CalledPropertyTopStmt{true, *t}
}

func (t *LocalStmt) toTopStmt() TopStmt {
	return &LocalTopStmt{*t}
}

func (t *ExistStmt) toTopStmt() TopStmt {
	return nil
}
