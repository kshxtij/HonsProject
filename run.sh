if [ -f install.log ]; then
  mv install.log logs/install.log.$(TZ="Europe/London" date "+%Y-%m-%d-%H:%M:%S").bak
fi

time ./install.sh $1 $2 2>&1 | tee install.log