START=$(date +%s)
(time ./install.sh "$1" "allyesconfig") 2>&1 | tee install.log
echo "\n\n" >> install.log
(time ./install.sh "$1" "defconfig") 2>&1 | tee -a install.log
echo "\n\n" >> install.log
END=$(date +%s)
echo "Installation took $(($END - $START)) seconds" >> install.log
mv ./install.log logs/install-$(TZ="Europe/London" date "+%Y-%m-%d-%H:%M:%S").log