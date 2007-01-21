TAR = tar

VERSION = $(shell date +%Y-%m-%d)
TARFILE = "../rz-alpha-$(VERSION).tar.gz"

release:
	(cd src && make clean)
	echo "RZ Version ALPHA $(VERSION)" > VERSION
	$(TAR) --create --file=$(TARFILE) --compress --verbose --directory=.. --exclude='*/.svn' --exclude='rz/private' --exclude='rz/Makefile' rz
	echo "Created $(TARFILE)"
