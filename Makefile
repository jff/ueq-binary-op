lhs:
	lhs2TeX --poly ueq-binary-op.lhs -o ueq-binary-op.tex
	latex ueq-binary-op.tex
	dvips ueq-binary-op
	dvipdf ueq-binary-op
