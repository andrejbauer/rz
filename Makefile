TAR = tar

VERSION = $(shell date +%Y-%m-%d)
BASENAME = rz-alpha-$(VERSION).tar.gz
TARFILE = ../$(BASENAME)

release: $(TARFILE)

$(TARFILE):
	(cd src && make clean)
	echo "RZ Version ALPHA $(VERSION)" > VERSION
	$(TAR) --create --file=$(TARFILE) --gzip --verbose --directory=.. --exclude='*/.svn' --exclude='rz/private' --exclude='rz/Makefile' rz
	echo "Created $(TARFILE)"

publish: $(TARFILE)
	scp $(TARFILE) shivaree.andrej.com:/var/www/rz
	ssh shivaree.andrej.com 'cd /var/www/rz; rm -f rz.tar.gz; ln -s $(BASENAME) rz.tar.gz'
