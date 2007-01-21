TAR = tar

release:
	(cd src && make clean)
	VERSION=`date +%Y-%m-%d`
	TARFILE="rz-alpha-$VERSION.tar.gz"
	echo "RZ Version ALPHA `date`" > VERSION
	$(TAR) --create --file=$TARFILE --compress --verbose --directory=.. --exclude='*/.svn' --exclude='rz/private' --exclude='rz/Makefile' rz
	echo "Created ${TARFILE}"
