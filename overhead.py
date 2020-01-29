import numpy as np
import matplotlib.pyplot as plt

# plt.rcParams.update({'font.size': 14})

benchmarks = ['GLM', 'L2SVM', 'ALS', 'PNMF', 'MLR']

N = len(benchmarks)

results = [
  {
    "method": "w/o sampling, greedy extraction",
    "translation": (1, 3, 2, 1, 2),
    "saturation" : (8, 13, 9, 12, 18),
    "extraction" : (5, 4, 3, 6, 4),
    "sysml" : (0, 0, 0, 0, 0)
  },
  {
    "method": "w/ sampling, greedy extraction",
    "translation": (1, 3, 2, 1, 2),
    "saturation" : (2, 1, 3, 2, 3),
    "extraction" : (2, 4, 3, 1, 2),
    "sysml" : (0, 0, 0, 0, 0)
  },
  {
    "method": "w/ sampling, ILP extraction",
    "translation": (1, 3, 2, 1, 2),
    "saturation" : (2, 1, 3, 2, 3),
    "extraction" : (7, 8, 13, 7, 6),
    "sysml" : (0, 0, 0, 0, 0)
  },
  {
    "method": "SystemML",
    "translation": (0, 0, 0, 0, 0),
    "saturation" : (0, 0, 0, 0, 0),
    "extraction" : (0, 0, 0, 0, 0),
    "sysml" : (0.3, 0.2, 0.5, 0.7, 0.8)
  },
]
ind = np.arange(N)    # the x locations for the groups
width = 0.35       # the width of the bars: can also be len(x) sequence

fig, axs = plt.subplots(1, 4, sharey=True, figsize=(12, 4), gridspec_kw={'wspace': 0})

(ax1, ax2, ax3, ax4) = axs
ax1.set_ylabel(ylabel='Compile Time [sec]')

for i, ax in enumerate(axs.flat):
  ax.set_xticks(np.arange(N))
  ax.set_xticklabels(benchmarks)
  benchmark = results[i]
  translation=benchmark["translation"]
  saturation =benchmark["saturation"]
  extraction =benchmark["extraction"]
  systemml =benchmark["sysml"]
  ax.bar(ind, translation, width, label='translate', color='0.2', ec='black')
  ax.bar(ind, saturation, width, label='saturate', bottom=translation, color='0.5', ec='black')
  ax.bar(ind, extraction, width, label='extract', bottom=saturation, color='white', ec='black', hatch='//')
  ax.bar(ind, systemml, width, label='SystemML', color='white', ec='black')
  ax.set_title(benchmark["method"])

ax4.legend()
# plt.legend((p1[0], p2[0], p3[0]), ('translation', 'saturation', 'extraction'))

plt.tight_layout()
plt.savefig('compiletime.pdf', format='pdf')
