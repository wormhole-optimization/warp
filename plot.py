import matplotlib
import matplotlib.pyplot as plt
import numpy as np

plt.style.use('grayscale')

# k-means
labels = ['1M rows\n10 cols', '1M rows\n100 cols', '10M rows\n10 cols', '10M rows\n100 cols']
opt0 = [13.345, 22.8758, 114.7328, 217.0804]
opt2_nofuse = [5, 6, 41, 75.1746]
opt2_fuse = [4, 4.8, 33, 60]
saturate_la = [5, 6, 41, 75]

x = np.arange(len(labels))
width = 0.2

fig, axs = plt.subplots(1, 5,  figsize=(20,4))

ax = axs[0]
opt0 =        ax.bar(x, opt0,        width, label='SystemML opt0', ec='black', color='0.2')
opt2_nofuse = ax.bar(x, opt2_nofuse, width, label='SystemML opt2', ec='black', color='0.5')
opt2_fuse =   ax.bar(x, opt2_fuse,   width, label='saturate w/RA', ec='black', color='white')
saturate_la = ax.bar(x, saturate_la, width, label='saturate w/LA', ec='black', color='white', hatch='//')

ax.set_ylabel('Execution Time [sec]')
ax.set_title('K-Means Execution Time')
ax.set_xticks(x)
ax.set_xticklabels(labels)
ax.set_yscale('log')
ax.legend()

# linregcg
labels = ['1M rows\n10 cols', '1M rows\n100 cols', '10M rows\n10 cols', '10M rows\n100 cols']
opt0 = [5.0288, 7.7834, 10.086, 27.878]
opt2_nofuse = [1.1922, 1.5462, 3.8562, 3.7554]
opt2_fuse = [0.4, 0.5, 1.3006, 1.227]

x = np.arange(len(labels))
width = 0.25

ax = axs[1]
opt0 =        ax.bar(x - width, opt0,        width, ec='black', color='0.2')
opt2_nofuse = ax.bar(x            , opt2_nofuse, width, ec='black', color='0.5')
opt2_fuse =   ax.bar(x + width, opt2_fuse,   width, ec='black', color='white')

ax.set_ylabel('Execution Time [sec]')
ax.set_title('Linear Regression Execution Time')
ax.set_xticks(x)
ax.set_xticklabels(labels)
ax.set_yscale('log')
ax.legend()

# l2svm
labels = ['1M rows\n10 cols', '1M rows\n100 cols', '10M rows\n10 cols', '10M rows\n100 cols']
opt0 = [16.2644, 23.859, 94.4358, 162.403]
opt2_nofuse = [9.2044, 9.4606, 71.8094, 97.2754]
opt2_fuse = [2.3, 2.4, 18, 24]

x = np.arange(len(labels))
width = 0.25

ax = axs[2]
opt0 =        ax.bar(x , opt0,        width, ec='black', color='0.2')
opt2_nofuse = ax.bar(x , opt2_nofuse, width, ec='black', color='0.5')
opt2_fuse =   ax.bar(x , opt2_fuse,   width, ec='black', color='white')

ax.set_ylabel('Execution Time [sec]')
ax.set_title('2-Layer SVM Execution Time')
ax.set_xticks(x)
ax.set_xticklabels(labels)
ax.set_yscale('log')
ax.legend()


ax = axs[3]
opt0 =        ax.bar(x , opt0,        width, ec='black', color='0.2')
opt2_nofuse = ax.bar(x , opt2_nofuse, width, ec='black', color='0.5')
opt2_fuse =   ax.bar(x , opt2_fuse,   width, ec='black', color='white')

ax.set_ylabel('Execution Time [sec]')
ax.set_title('2-Layer SVM Execution Time')
ax.set_xticks(x)
ax.set_xticklabels(labels)
ax.set_yscale('log')
ax.legend()

ax = axs[4]
opt0 =        ax.bar(x - width, opt0,        width, ec='black', color='0.2')
opt2_nofuse = ax.bar(x            , opt2_nofuse, width, ec='black', color='0.5')
opt2_fuse =   ax.bar(x + width, opt2_fuse,   width, ec='black', color='white')

ax.set_ylabel('Execution Time [sec]')
ax.set_title('2-Layer SVM Execution Time')
ax.set_xticks(x)
ax.set_xticklabels(labels)
ax.set_yscale('log')
ax.legend()

plt.show()
