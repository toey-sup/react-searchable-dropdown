import { useState } from 'react';
import { Story } from "@storybook/react";
import { Meta } from "@storybook/react/types-6-0";
import { Selector, SelectorProps, Choice } from "./Selector";
import { words } from '../../.storybook/const';

const choices: Choice[] = words.map((word) => ({ label: word, id: word }));

export default {
  title: "Components/Selector",
  component: Selector,
  args: {
    label: '',
    popUpKey: 'Selector-key',
    choiceSections: [{ choices }],
    name: 'Choice',
    placeholder: 'please select a choice',
    id: 'Selector-id',
    handleSelect: () => { return null; },
    style: { width: '300px' }
  },
  argTypes: {
    handleSelect: { action: 'clicked' },
  }
} as Meta<SelectorProps>;


const Template: Story<SelectorProps> = (args) => {
  const [label, setLabel] = useState<string>('');
  return (
    <Selector
      {...args}
      label={label}
      handleSelect={({ value }) => { setLabel(value.label); }}
    />
  );
};

export const NormalSelector = Template.bind({});
NormalSelector.args = { ...Template.args };

export const SelectorWithSectionPrefix = Template.bind({});
SelectorWithSectionPrefix.args = { ...Template.args, choiceSections: [{ sectionName: 'Special Choice', sectionPrefix: 'Special', choices: [{ label: 'Special One'}, { label: 'Special Two'}, { label: 'Special Three'}, { label: 'Special Four'}]}, { sectionName: 'Normal Choice', choices, sectionPrefix: 'Normal' }] };

export const SelectorWithUsedChoices = Template.bind({});
SelectorWithUsedChoices.args = { ...Template.args, choiceSections: [{ choices: words.map((word, index) => ({ label: word, id: word, used: index < 10 })) }] };

