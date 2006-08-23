#!/bin/bash

RZ=../rz
DIFF=diff
BASENAME=basename

VALIDATE=0
if [ "$1" = "-v" ]
    then
    VALIDATE=1
fi

for FILE in *.thy
  do
  $RZ --nosave $FILE &> $FILE.out
  if [ -f $FILE.ref ]
      then
      RESULT=`$DIFF $FILE.out $FILE.ref`
      if [ "$?" = "0" ]
	  then
	  echo "Passed:  $FILE"
      else
	  echo "FAILED:  $FILE"
	  if [ $VALIDATE = "1" ]
	      then
	      echo $RESULT
	      read -p 'Validate? (Y/n) ' ans
	      if [ "$ans" = "" -o "$ans" = "y" -o "$ans" = "Y" ]
		  then
		  mv $FILE.out $FILE.ref
		  echo Validated: $FILE
	      fi
	  fi
      fi
      
  else
      mv $FILE.out $FILE.ref
      echo Created: $FILE.ref
  fi
done
