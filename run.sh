time ./install.sh $1 2>&1 | tee install.log
mv ./install.log logs/install-$(TZ="Europe/London" date "+%Y-%m-%d-%H:%M:%S").log