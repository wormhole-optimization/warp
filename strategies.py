import matplotlib.pyplot as plt
import numpy as np

# plt.rcParams.update({'font.size': 13})
# plt.rcParams["font.family"] = "Times New Roman"

fig, axs = plt.subplots(
    1, 5,
    sharey=True,
    figsize=(12, 4),
    gridspec_kw={'wspace': 0}
)

ax1, ax2, ax3, ax4, ax5 = axs
ax3.set_xlabel('Data Size (Input Dimensions)')
ax1.set_ylabel(ylabel='Run Time [sec]') #, labelpad=-2)
ax1.set_yscale('log')

width = 0.2

# GLM L2SVM MLogReg ALS PNMF

results = [
# k-means
    {
        "name" : "ALS",
        "opt0" : [13.345, 22.8758, 114.7328],
        "opt2" : [1.5, 2, 14],
        "saturate_ra" : [1.5, 2, 14],
        "saturate_la" : [1.5, 2, 14]
    },
    {
        "name" : "GLM",
        "opt0" : [10.345, 20.8758, 104.7328],
        "opt2" : [3, 5, 31],
        "saturate_ra" : [3, 5, 31],
        "saturate_la" : [3, 5, 31],
    },
    {
        "name" : "L2SVM",
        "opt0" : [23.345, 32.8758, 174.7328],
        "opt2" : [15, 22, 81],
        "saturate_ra" : [15, 22, 81],
        "saturate_la" : [15, 22, 81],
    },
    {
        "name" : "MLogReg",
        "opt0" : [12.345, 24.8758, 134.7328],
        "opt2" : [4, 4.8, 33],
        "saturate_ra" : [4, 4.8, 33],
        "saturate_la" : [4, 4.8, 33],
    },
    {
        "name" : "PNMF",
        "opt0" : [20.345, 35.8758, 104.7328],
        "opt2" : [2, 2.8, 23],
        "saturate_ra" : [2, 2.8, 23],
        "saturate_la" : [2, 2.8, 23],
    }
]

labels = ['1Mx10', '10Mx10', '10Mx100']
x = np.arange(len(labels))

for i, ax in enumerate(axs.flat):

    benchmark = results[i]
    ax.bar(x-1.5*width, benchmark["opt0"],        width, label='SystemML',      ec='black', color='0.2')
    ax.bar(x-0.5*width, benchmark["opt2"],        width, label='F+greedy',    ec='black', color='0.5')
    ax.bar(x+0.5*width, benchmark["saturate_la"], width, label='S+ILP', ec='black', color='white', hatch='//')
    ax.bar(x+1.5*width, benchmark["saturate_ra"], width, label='S+greedy', ec='black', color='white')

    ax.set_title(benchmark["name"])
    ax.set_xticks(x)
    ax.set_xticklabels(labels)
    ax.label_outer()

ax1.legend()

plt.tight_layout()
plt.savefig('strategy.pdf')
