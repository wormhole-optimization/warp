import matplotlib.pyplot as plt
import numpy as np

plt.rcParams.update({'font.size': 9})
# plt.rcParams["font.family"] = "Times New Roman"

fig, axs = plt.subplots(
    2, 3,
    sharey=True,
    figsize=(5, 4),
    gridspec_kw={'wspace': 0}
)
# add a big axes, hide frame
# fig.add_subplot(111, frameon=False)
# hide tick and tick label of the big axes
# plt.tick_params(labelcolor='none', top='off', bottom='off', left='off', right='off')

((ax1, ax2, ax3), (ax4, ax5, ax6)) = axs
ax5.set_xlabel('Dataset')
ax1.set_ylabel(ylabel='Run Time [sec]') #, labelpad=-2)
ax4.set_ylabel(ylabel='Run Time [sec]') #, labelpad=-2)
ax1.set_yscale('log')

width = 0.35

# GLM L2SVM MLogReg ALS PNMF

results = [
# k-means
    {
        "name" : "ALS",
        "opt2" :[45.4906, 97.8884, 213.1432, 19.5088, 52.7206, 115.8852],
        "saturate_ra" :[6.7214, 8.7494, 21.6916, 9.0214, 9.0134, 19.355],
    },
    {
        "name" : "PNFM",
        "opt2" :[12.549, 24.5796, 46.1356, 6.0964, 11.7034, 25.624],
        "saturate_ra" :[4.1996, 4.8156, 13.7282, 3.3746, 3.8, 8.7208],
    },
    {
        "name" : "L2SVM",
        "opt2" :[44.652, 116.896, 127.301, 8.2, 13.198, 22.176],
        "saturate_ra" : [43.293, 119.038, 120.177, 8.019, 13.32, 22.316],
    },
    {
        "name" : "MLogReg",
        "opt2" :[28.5652, 54.0564, 100.579, 72.5446, 157.29, 191.2482],
        "saturate_ra" :[20.0234, 34.5428, 63.7024, 56.7206, 125.2508, 165.1192],
    },
    {
        "name" : "GLM",
        "opt2" :[71.816, 170.835, 237.993, 13.575, 22.215, 40.178],
        "saturate_ra" :[72.96, 165.019, 218.029, 14.481, 22.851, 38.885]
    }
]

labels = ['A', 'B', 'C', 'A', 'B', 'C']
x = np.arange(len(labels))

for i, ax in enumerate(axs.flat):

    if i == 5:
      break
    if i in [1, 2, 4]:
      ax.yaxis.set_ticks_position('none')
    benchmark = results[i]
    ax.bar(x-0.5*width, benchmark["opt2"],        width, label='SystemML',    ec='black', color='0.5')
    ax.bar(x+0.5*width, benchmark["saturate_ra"], width, label='SPORES', ec='black', color='white')

    ax.set_title(benchmark["name"])
    ax.set_xticks(x)
    ax.set_xticklabels(labels)
    ax.label_outer()

fig.delaxes(ax6)
handles, labels = ax5.get_legend_handles_labels()
ax5.legend(loc='center left', bbox_to_anchor=(1.1, 0.5))
# fig.legend(handles, labels, loc='lower left', ncol = 2, bbox_to_anchor=(0.15,0))

# plt.xlabel('Dataset')
plt.ylim(top=1000)
plt.ylim(bottom=1)
plt.tight_layout()
plt.savefig('runtime.pdf')
