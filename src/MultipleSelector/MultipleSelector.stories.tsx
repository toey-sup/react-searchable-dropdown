import { useState } from 'react';
import { Story } from "@storybook/react";
import MultipleSelector, { Props, Choice } from "./MultipleSelector";
import { Meta } from "@storybook/react/types-6-0";
import { words } from '../../.storybook/const';

const choices: Choice[] = words.map((word) => ({ label: word, id: word }));

export default {
  title: "Components/MultipleSelector",
  component: MultipleSelector,
  args: {
    label: '',
    popUpKey: 'MultipleSelector-key',
    choiceSections: [{ choices }],
    name: 'Choice',
    placeholder: 'please select a choice',
    id: 'MultipleSelector-id',
    handleSelect: () => { return null; },
    style: { width: '300px' }
  },
  argTypes: {
    handleSelect: { action: 'clicked' },
  }
} as Meta<Props>;


const Template: Story<Props> = (args) => {
  const [checkedChoices, setCheckedChoices] = useState<Choice[]>([]);
  return (
    <MultipleSelector
      {...args}
      label={(checkedChoices.length <= 1) ? checkedChoices[0]?.label || '' : `${checkedChoices[0]?.label} & ${checkedChoices.length - 1} More`}
      handleSelect={({ value, name }: { value: Choice[], name: string}) => { setCheckedChoices(value); }}
      checkedChoices={checkedChoices}
      />
  );
};

export const NormalMultipleSelector = Template.bind({});
NormalMultipleSelector.args = { ...Template.args };

export const MultipleSelectorWithSingleChoice = Template.bind({});
MultipleSelectorWithSingleChoice.args = { ...Template.args, choiceSections:[{ sectionName: 'Single Choice', choices: [{ label: 'Special One', singleChoice: true }]}, { sectionName: 'Multiple Choice', choices }]};

export const MultipleSelectorWithSectionPrefix = Template.bind({});
MultipleSelectorWithSectionPrefix.args = { ...Template.args, choiceSections: [{ sectionName: 'Single Choice', sectionPrefix: 'single-prefix', choices: [{ label: 'Special One', singleChoice: true }]}, { sectionName: 'Multiple Choice', choices, sectionPrefix: 'mul-prefix' }] };

export const MultipleSelectorWithUsedChoices = Template.bind({});
MultipleSelectorWithUsedChoices.args = { ...Template.args, choicesSections: [{ choices: words.map((word, index) => ({ label: word, id: word, used: index < 10 })) }] };
