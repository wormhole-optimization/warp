import matplotlib.pyplot as plt
import numpy as np

plt.rcParams.update({'font.size': 13})

width = 0.2

fig, ax = plt.subplots()

# k-means
labels = ['GLM', 'L2SVM', 'MLogReg', 'ALS', 'PNMF']
opt0 = [13.345, 22.8758, 114.7328, 114.7328, 114.7328]
opt2_nofuse = [5, 6, 41, 41, 41]
opt2_fuse = [4, 4.8, 4.8, 4.8, 33]

x = np.arange(len(labels))
ax.set_ylabel(ylabel='Compile Time [sec]', labelpad=-6)

ax.bar(x-1.5*width, opt0,        width, label='SystemML', ec='black', color='0.2')
ax.bar(x-0.5*width, opt2_nofuse, width, label='ILP', ec='black', color='0.5')
ax.bar(x+0.5*width, opt2_fuse,   width, label='greedy', ec='black', color='white')

ax.set_xticks(x)
ax.set_xticklabels(labels)
ax.legend()
ax.set_xlabel('Algorithm')

ax.label_outer()

yl = plt.ylim()

plt.tight_layout()
plt.savefig('compilevsml.pdf', format='pdf')
