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
	      echo ---- $DIFF --side-by-side $FILE.out $FILE.ref ----
	      $DIFF --side-by-side -W200 $FILE.out $FILE.ref
	      echo -----------------------------------
	      read -p "Validate $FILE.out as new $FILE.ref? (y/n) [n] " ans
	      if [ "$ans" = "y" -o "$ans" = "Y" ]
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
