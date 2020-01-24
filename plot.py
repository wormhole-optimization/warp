import matplotlib
import matplotlib.pyplot as plt
import numpy as np

plt.style.use('grayscale')

# k-means
labels = ['1M rows\n10 cols', '1M rows\n100 cols', '10M rows\n10 cols', '10M rows\n100 cols']
opt0 = [13.345, 22.8758, 114.7328, 217.0804]
opt2_nofuse = [5.236, 6.692, 41.2514, 75.1746]
opt2_fuse = [5.0652, 6.4712, 46.384, 65.877]

x = np.arange(len(labels))
width = 0.25

fig, ax = plt.subplots()
opt0 =        ax.bar(x - width, opt0,        width, label='opt0', ec='black', color='0.2')
opt2_nofuse = ax.bar(x            , opt2_nofuse, width, label='opt2_nofuse', ec='black', color='0.5')
opt2_fuse =   ax.bar(x + width, opt2_fuse,   width, label='opt2_fuse', ec='black', color='white')

ax.set_ylabel('Execution Time [sec]')
ax.set_title('K-Means Execution Time')
ax.set_xticks(x)
ax.set_xticklabels(labels)
ax.legend()

# linregcg
labels = ['1M rows\n10 cols', '1M rows\n100 cols', '10M rows\n10 cols', '10M rows\n100 cols']
opt0 = [5.0288, 7.7834, 10.086, 27.878]
opt2_nofuse = [1.1922, 1.5462, 3.8562, 3.7554]
opt2_fuse = [1.1666, 1.43, 3.3006, 4.227]

x = np.arange(len(labels))
width = 0.25

fig, ax = plt.subplots()
opt0 =        ax.bar(x - width, opt0,        width, label='opt0', ec='black', color='0.2')
opt2_nofuse = ax.bar(x            , opt2_nofuse, width, label='opt2_nofuse', ec='black', color='0.5')
opt2_fuse =   ax.bar(x + width, opt2_fuse,   width, label='opt2_fuse', ec='black', color='white')

ax.set_ylabel('Execution Time [sec]')
ax.set_title('Linear Regression Execution Time')
ax.set_xticks(x)
ax.set_xticklabels(labels)
ax.legend()

# l2svm
labels = ['1M rows\n10 cols', '1M rows\n100 cols', '10M rows\n10 cols', '10M rows\n100 cols']
opt0 = [16.2644, 23.859, 94.4358, 162.403]
opt2_nofuse = [9.2044, 9.4606, 71.8094, 97.2754]
opt2_fuse = [7.1232, 8.327, 57.2872, 87.5194]

x = np.arange(len(labels))
width = 0.25

fig, ax = plt.subplots()
opt0 =        ax.bar(x - width, opt0,        width, label='opt0', ec='black', color='0.2')
opt2_nofuse = ax.bar(x            , opt2_nofuse, width, label='opt2_nofuse', ec='black', color='0.5')
opt2_fuse =   ax.bar(x + width, opt2_fuse,   width, label='opt2_fuse', ec='black', color='white')

ax.set_ylabel('Execution Time [sec]')
ax.set_title('2-Layer SVM Execution Time')
ax.set_xticks(x)
ax.set_xticklabels(labels)
ax.legend()



plt.show()
