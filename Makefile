TAR = tar
OUTFILE = ../rz.tar.gz

release:
	(cd src && make clean)
	echo "RZ Version ALPHA `date`" > VERSION
	$(TAR) --create --file=$(OUTFILE) --compress --verbose --directory=.. --exclude='*/.svn' --exclude='rz/private' --exclude='rz/Makefile' rz
	echo "Created $(OUTFILE)"
