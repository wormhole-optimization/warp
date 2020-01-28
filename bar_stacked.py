import numpy as np
import matplotlib.pyplot as plt

# plt.rcParams.update({'font.size': 14})

N = 5
translation = (1, 3, 2, 1, 2)
saturation = (5, 7, 14, 8, 5)
extraction = (5, 4, 9, 7, 5)
ind = np.arange(N)    # the x locations for the groups
width = 0.35       # the width of the bars: can also be len(x) sequence

fig, axs = plt.subplots(1, 3, sharex=True, sharey=True, figsize=(12, 4))

(ax1, ax2, ax3) = axs
ax1.set_ylabel(ylabel='Compile Time [sec]')
ax2.set_xlabel(xlabel='Algorithm')

for ax in axs.flat:

  p1 = ax.bar(ind, translation, width, color='0.2', ec='black')
  p2 = ax.bar(ind, saturation, width, bottom=translation, color='0.5', ec='black')
  p3 = ax.bar(ind, extraction, width, bottom=saturation, color='white', ec='black')

plt.xticks(ind, ('GLM', 'L2SVM', 'ALS', 'PNMF', 'MLogReg'))
# plt.legend((p1[0], p2[0], p3[0]), ('translation', 'saturation', 'extraction'))

plt.tight_layout()
plt.savefig('compiletime1.pdf', format='pdf')
